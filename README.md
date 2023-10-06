# Essence of Demand-Driven Execution (DDE)

[![Build & test
project](https://github.com/JHU-PL-Lab/dde/actions/workflows/build.yml/badge.svg)](https://github.com/JHU-PL-Lab/dde/actions/workflows/build.yml)

This repo contains a [concrete](./interpreter) and an
[abstract](./program_analysis) interpreter based on DDE, as well as
[formalizations](./formal) in Coq.

## Set up

Before building the project, install `fbdk` locally so that it is visible to
this project:

```sh
cd PATH_TO_FbDK_REPO
git checkout fbenv # checkout to the fbenv branch first
opam install .
```

Then `dune build` this project.

## Develop

### utop

`dune utop` to start an interactive environment with all libraries loaded.
Or, `dune utop interpreter`, `dune utop program_analysis`, `dune utop
interpreter/access_links` to run each separately.

```ocaml
open Interpreter;; (* first if only working with program analysis *)

open Debugutils;; (* to simplify calling utility functions such as `peu` *)

is_debug_mode := true;; (* to print debug information from the
concrete interpretation. *)

should_simplify := true;; (* to perform variable substitution, function
application, etc. on the concrete interpretation result. *)
```

### Binary

`dune exec interpreter/main.exe` to run the interpreter. Same applies
to `program_analysis/main.exe`.

Optionally pass in the `--debug` flag to print debug information from the
evaluation:

```sh
dune exec -- interpreter/main.exe --debug
```

Optionally pass in a file name to run the interpreter on the file:

```sh
dune exec -- interpreter/main.exe <path-to-file> --debug
```

Same applies to `--simplify`.

## Testing

`dune test` to run the associated test suite *without* benchmarking.

To also benchmark the DDE interpreter's performance, pass in the `--bench` flag:

```sh
dune exec -- tests/tests.exe --bench
``` 

`bisect-ppx-report html` or `bisect-ppx-report summary` to view coverage.

# Formalizations

Please refer to [formal/README.md](./formal/README.md) for details.
