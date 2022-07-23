# yatima-lang

A compiler and typechecker for the Yatima language.

## Build

Build it with `lake build`.

## Install

Run `lake script run setup`, which will build the `yatima` binary and ask you where to place it.
You can choose a directory that's already in your path, for example.

## Usage

### Storing Lean objects

Call `yatima store arg1 arg2 ...`, where each `argN` is either a Lean file or a directory of Lean files.

Optional flags:
* `--prelude` (or `-p`) optimizes the compilation of prelude files without imports.
All files to be compiled must follow this rule
* `--log` (or `-l`) logs compilation progress
* `--summary` (or `-s`) prints a compilation summary at the end of the process

Constraints:
* The `store` command must be triggered from within a Lean project that uses Lake
* The compiled code must use the same toolchain as the one used to compile the `yatima` binary.
To see the needed toolchain, call `yatima --version` and check the content before the pipe `|`.
* To compile a file that imports others, the imported `olean` files must be available
