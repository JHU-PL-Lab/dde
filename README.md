# Essence of Demand-Driven Execution (DDE)

This repo contains a [concrete](./interpreter) and an [abstract interpreter](./program_analysis) based on DDE.

## Set up

Before building the project, opam install `fbdk` so that it is visible to this
project:

```sh
opam install <path-to-local-fbdk-dist>
```

Then `dune build`.

## Develop

### utop

`dune utop` to start an interactive environment with all libraries loaded.
Or, `dune utop <interpreter/program_analysis>` to load either the concrete or
the abstract interpreter.

```ocaml
open Program_analysis;; (* first if only working with program analysis *)

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
