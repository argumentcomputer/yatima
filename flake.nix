{
  description = "Yatima Language";

  inputs = {
    lean = {
      url = github:leanprover/lean4;
      inputs.flake-utils.follows = "flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    ipld = {
      url = github:yatima-inc/Ipld.lean;
      inputs.lean.follows = "lean";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    nixpkgs.url = github:nixos/nixpkgs/nixos-21.11;
    naersk = {
      url = github:nix-community/naersk;
      inputs.flake-utils.follows = "flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils = {
      url = github:numtide/flake-utils;
      inputs.nixpkgs.follows = "nixpkgs";
    };
    utils = {
      url = github:yatima-inc/nix-utils;
      inputs.flake-utils.follows = "flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.naersk.follows = "naersk";
    };
  };

  outputs = { self, lean, flake-utils, utils, nixpkgs, naersk, ipld }:
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
        lib = utils.lib.${system};
        inherit (lib) buildRustProject getRust;
        rustNightly = getRust { date = "2022-05-12"; sha256 = "sha256-ttn4r8k3yzreTgsMSJAg37uZWHuZBPUDsBhJDkASyWM="; };
        yatima-rs = buildRustProject {
          rust = rustNightly;
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
