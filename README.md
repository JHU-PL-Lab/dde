# Essence of Demand-Driven Execution (DDE)

This repo contains an interpreter for DDE.

## Set up

Before building the project, opam install `fbdk` so that it is visible to this
project:

```sh
opam install <path-to-local-fbdk-dist>
```

## Develop

`dune utop` to start an interactive environment with DDE. `open
Debugutils;;` to simplify calling helper functions such as `peu`.

## Testing

`dune test` to run the associated test suite. `bisect-ppx-report html` or
`bisect-ppx-report summary` to view coverage.