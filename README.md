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
```

### Binary

`dune exec src/interpreter.exe` to run the interpreter.

Optionally pass in the `--debug` flag to print debug information from the
evaluation:

```sh
dune exec src/interpreter.exe -- --debug
```

Optionally pass in a file name to run the interpreter on the file:

```sh
dune exec src/interpreter.exe -- <path-to-file> --debug
```

## Testing

`dune test` to run the associated test suite. `bisect-ppx-report html` or
`bisect-ppx-report summary` to view coverage.