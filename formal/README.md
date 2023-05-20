# DDE Formalizations

Current progress:
- [ ] concrete operational semantics
  - [x] demand-driven
    - [x] deterministic
  - [ ] environment/closure-based
  - [ ] equivalence among concrete operational semantics
- [ ] abstract (program analysis) operational semantics
  - [x] non-deterministic demand-driven
    - [ ] non-deterministic
  - [x] all-paths
    - [ ] deterministic
  - [ ] standard
  - [ ] Soundness with respect to concrete semantics
  - [ ] Greater precision of demand-driven semantics

## Set up

Follow the [official instructions](https://coq.inria.fr/download) to install Coq.

## Develop

`dune build` or `dune build formal` from the repo root, then use your preferred
IDE to step through the scripts.

If you're using VSCode, I recommend installing the
[VSCoq](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq)
extension.
