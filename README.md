# yatima

Yatima is a Lean 4 compiler backend targeting the [the Lurk language](https://lurk-lang.org/) for recursive zkSNARKs, enabling zero-knowledge proofs of Lean 4 execution.
Additionally, Yatima has its own Lean 4 implementation of a kernel for the Lean 4 core language, which can be compiled to Lurk to allow zero-knowledge proofs of Lean 4 typechecking.
By verifying a zero knowledge proof that a Lean 4 declaration has passed the typechecker, one can verify that the declaration is type-safe without re-running the typechecker.

Yatima also implements nameless content-addressing for Lean 4, allowing each expression, declaration and environment to receive unique hash identifiers, independent of computationally-irrelevant naming (such as the names of definitions and local variables).

## Install

Run `lake run setup`, which will build the `yatima` binary and ask you where to place it.
You can choose a directory that's already in your path, for example.

Running the setup script will also compile the Yatima typechecker and store it in the FS, under the `$HOME/.cache/yatima_store` directory.

## Usage

The subcommands planned to be available for the `yatima` CLI are:
* Main commands
    * `ca`: content-addresses Lean 4 code to Yatima IR
    * `prove`: generates Lurk code for typechecking a content-addressed declaration
* Auxiliary commands
    * `tc`: typechecks Yatima IR
    * `gen`: generates Lurk code from Lean 4 code
    * `pin`: edits the `TypecheckM.lean` file with the hashes for primitive operations and allowed axioms
    * `gentc`: compiles the Yatima typechecker to Lurk
* Network
    * `ipfs put`: sends Yatima IR to IPFS
    * `ipfs get`: retrieves Yatima IR from IPFS

Don't hesitate to call `yatima --help` for more information.

Constraints:
* The `ca` subcommand must be triggered from within a Lean project that uses Lake
* The Lean 4 code to be content-addressed must use the same toolchain as the one used to compile the `yatima` binary.
To see the needed toolchain, call `yatima --version` and check the content before the pipe `|`
* To compile a Lean 4 file that imports others, the imported `olean` files must be available
