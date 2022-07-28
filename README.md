# yatima-lang

A WIP compiler and typechecker for the Yatima language.

## Build

Build it with `lake build`.

## Install

Run `lake script run setup`, which will build the `yatima` binary and ask you where to place it.
You can choose a directory that's already in your path, for example.

## Usage

The subcommands planned to be available for the `yatima` CLI are:
* `compile`: compile Lean 4 code to Yatima IR
* `typecheck`: typecheck Yatima IR
* `transpile`: transpile Yatima IR to Lurk code
* `pipe`: chain the three subcommands above without writing Yatima IR to disk
* `prove`: generates a Lurk proof that a certain Lean 4 declaration typechecks
* `verify`: verify the correctness of a Lurk proof

Constraints:
* The `compile` subcommand must be triggered from within a Lean project that uses Lake
* The Lean 4 code to be compiled must use the same toolchain as the one used to compile the `yatima` binary.
To see the needed toolchain, call `yatima --version` and check the content before the pipe `|`
* To compile a Lean 4 file that imports others, the imported `olean` files must be available
