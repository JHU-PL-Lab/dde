# Pure Demand Operational Semantics

[![Build & test
project](https://github.com/JHU-PL-Lab/dde/actions/workflows/build.yml/badge.svg)](https://github.com/JHU-PL-Lab/dde/actions/workflows/build.yml)

This repo contains pure demand [concrete](./interpreter) and
[abstract](./program_analysis) interpreters, as well as
[formalizations](./formal) in Coq.

## Set up

Before building the project (the concrete interpreter part), install `fbdk`
locally so that it is visible to this project:

```sh
cd PATH_TO_FbDK_REPO
git checkout fbenv # checkout to the fbenv branch first
opam install .
```

Then `dune build` this project.

> Note that you currently won't be able to run the interpreter tests if you
> don't have access to `fbdk`. We will soon provide a polished, fully
> executable artifact. For now, please build the program analysis separately
> via `dune build program_analysis`.

## Develop

### utop

`dune utop` to start an interactive environment with all libraries loaded.
Or, `dune utop program_analysis/full`, `dune utop interpreter/src` to run each separately.

```ocaml
open Interp;; (* first if only working with interpreter *)

open Debugutils;; (* to simplify calling utility functions such as `peu` *)

is_debug_mode := true;; (* to print debug information from the
concrete interpretation. *)

should_simplify := true;; (* to perform variable substitution, function
application, etc. on the concrete interpretation result. *)
```

### Binary

`dune exec interpreter/src/main.exe` to run the interpreter. Same applies
to `program_analysis/full/main.exe`.

Optionally pass in the `--debug` flag to print debug information from the
evaluation:

```sh
dune exec -- interpreter/src/main.exe --debug
```

Optionally pass in a file name to run the interpreter on the file:

```sh
dune exec -- interpreter/src/main.exe <path-to-file> --debug
```

Same applies to `--simplify`.

## Testing

`dune test` to run the associated test suite *without* benchmarking.

To also benchmark the interpreter's performance, pass in the `--bench` flag:

```sh
dune exec -- interpreter/tests/tests.exe --bench
``` 

`bisect-ppx-report html` or `bisect-ppx-report summary` to view coverage.

# Formalizations

Please refer to [formal/README.md](./formal/README.md) for details.
