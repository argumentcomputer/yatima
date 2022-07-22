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
The command must be triggered from within a Lean project that uses Lake.

The `store` subcommand accepts an optional `--log` (or `-l`) flag to trigger the compilation logs.

**Important**: If file `A` imports file `B` and you want to compile `A`, the `olean` file for `B` must be available.
