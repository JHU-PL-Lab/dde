★ Please see the [artifact](https://github.com/JHU-PL-Lab/dde/tree/artifact)
branch for the latest, condensed code.

[![Build & test
project](https://github.com/JHU-PL-Lab/dde/actions/workflows/build.yml/badge.svg)](https://github.com/JHU-PL-Lab/dde/actions/workflows/build.yml) [![DOI](https://zenodo.org/badge/569066625.svg)](https://zenodo.org/doi/10.5281/zenodo.10794349)

# Pure Demand Operational Semantics

This repo contains pure demand [concrete](./interpreter) and
[abstract](./program_analysis) interpreters, as well as
[formalizations](./formal) in Coq.

## Set up the project

Before building the project (the concrete interpreter part), install `fbdk`
locally so that it is visible to this project:

```sh
cd PATH_TO_FbDK_REPO
git checkout fbenv # checkout to the fbenv branch first
opam install .
```

Then `dune build` this project.

> Note that you currently won't be able to run the interpreter tests if you
> don't have access to `fbdk`. Please build the program analysis separately
> via `dune build program_analysis`. Go to the
> [artifact](https://github.com/JHU-PL-Lab/dde/tree/artifact) branch for a fully
> executable version.

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

To also benchmark the program analysis' performance, pass in the `--bench` flag:

```sh
dune exec -- program_analysis/tests/tests.exe --bench
``` 

`bisect-ppx-report html` or `bisect-ppx-report summary` to view coverage.

# Formalizations

Please refer to [formal/README.md](./formal/README.md) for details.
