# yatima-lang

A WIP tool for content-addressing and generating Lurk code from Lean 4 code.

## Build

Build it with `lake build`.

## Install

Run `lake run setup`, which will build the `yatima` binary and ask you where to place it.
You can choose a directory that's already in your path, for example.

## Usage

The subcommands planned to be available for the `yatima` CLI are:
* `ca`: content-addresses Lean 4 code to Yatima IR
* `ipfs put`: sends Yatima IR to IPFS
* `ipfs get`: retrieves Yatima IR from IPFS
* `tc`: typechecks Yatima IR
* `gen`: generates Lurk code from Lean 4 code
* `prove` (TODO): generates a Lurk proof that a certain Lean 4 declaration typechecks
* `verify` (TODO): verifies the correctness of a Lurk proof

Constraints:
* The `ca` subcommand must be triggered from within a Lean project that uses Lake
* The Lean 4 code to be content-addressed must use the same toolchain as the one used to compile the `yatima` binary.
To see the needed toolchain, call `yatima --version` and check the content before the pipe `|`
* To compile a Lean 4 file that imports others, the imported `olean` files must be available
