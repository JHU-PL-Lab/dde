# Essence of Demand-Driven Execution (DDE)

This repo contains an interpreter for DDE.

## Set up

Before building the project, opam install `fbdk` so that it is visible to this
project:

```sh
opam install <path-to-local-fbdk-dist>
```

Then `dune build`.

## Develop

### utop

`dune utop` to start an interactive environment with DDE.

```ocaml
open Debugutils;; (* to simplify calling utility functions such as `peu` *)

Debugutils.is_debug_mode := true;; (* or *)
is_debug_mode := true;; (* to print debug information from the
evaluation. *)

Debugutils.should_simplify := true;; (* or *)
should_simplify := true;; (* to perform variable substitution, function
application, etc. on the evaluation result. *)

```

### Binary

`dune exec interpreter/main.exe` to run the interpreter.

Optionally pass in the `--debug` flag to print debug information from the
evaluation:

```sh
dune exec --interpreter/main.exe --debug
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