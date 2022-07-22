{
  description = "Yatima Language";

  inputs = {
    lean = {
      url = "github:leanprover/lean4/v4.0.0-m5";
      inputs.flake-utils.follows = "flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    ipld = {
      url = "github:yatima-inc/Ipld.lean";
      inputs.lean.follows = "lean";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    yatima-std = {
      # url = "github:yatima-inc/YatimaStdLib.lean";
      url = "github:anderssorby/YatimaStdLib.lean/acs/add-flake";
      inputs.lean.follows = "lean";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    nixpkgs.url = "nixpkgs/nixos-unstable";
    naersk = {
      url = github:nix-community/naersk;
      inputs.flake-utils.follows = "flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils = {
      url = "github:numtide/flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, lean, flake-utils, nixpkgs, naersk, ipld, yatima-std, fenix }:
    let
      supportedSystems = [
        # "aarch64-linux"
        # "aarch64-darwin"
        # "i686-linux"
        # "x86_64-darwin"
        "x86_64-linux"
      ];
    in
    flake-utils.lib.eachSystem supportedSystems (system:
      let
        leanPkgs = lean.packages.${system};
        pkgs = nixpkgs.legacyPackages.${system};
        rust = fenix.packages.${system}.complete;
        inherit (rust) cargo rustc;
        # Get a naersk with the input rust version
        naerskWithRust = rust: naersk.lib."${system}".override {
          inherit (rust) cargo rustc;
        };
        env = with pkgs; {
          LIBCLANG_PATH = "${llvmPackages.libclang.lib}/lib";
        };
        # Naersk using the default rust version
        buildRustProject = pkgs.makeOverridable ({ naersk ? naerskWithRust rust, ... } @ args: with pkgs; naersk.buildPackage ({
          buildInputs = [
            clang
            pkg-config
          ] ++ lib.optionals stdenv.isDarwin [
            darwin.apple_sdk.frameworks.Security
          ];
          copyLibs = true;
          copyBins = true;
          targets = [ ];
          remapPathPrefix =
            true; # remove nix store references for a smaller output package
        } // env // args));
        yatima-rs = buildRustProject {
          src = ./yatima-rs;
          copyLibs = true;
        };
        project = leanPkgs.buildLeanPackage {
          debug = false;
          deps = [ ipld.project.${system} ];
          name = "Yatima";
          src = ./.;
        };
        main = leanPkgs.buildLeanPackage {
          debug = false;
          deps = [ project ];
          name = "Main";
          src = ./.;
        };
      in
      {
        inherit project;
        packages = {
          inherit yatima-rs;
          inherit (project) modRoot sharedLib staticLib lean-package executable;
          inherit (leanPkgs) lean;
          main = main.executable;
        };

        defaultPackage = main.executable;
      });
}
