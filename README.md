# yatima-lang

A compiler and typechecker for the Yatima language.

## Build

Build it with `lake build`.

## Usage

### Storing Lean objects

Call `yatima store arg1 arg2 ...`, where each `argN` is either a Lean file or a directory of Lean files.
The command must be triggered from within a Lean project that uses Lake.

The `store` subcommand accepts an optional `--log` (or `-l`) flag to trigger the compilation logs.
