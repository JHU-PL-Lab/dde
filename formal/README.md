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
  - [ ] equivalence among abstract opertional semantics
- [ ] Soundness of program analyses

## Set up

Follow the [official instructions](https://coq.inria.fr/download) to install Coq.

## Develop

`dune build`, then use your preferred IDE to step through the scripts.

If you're using VSCode, I recommend installing the
[VSCoq](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq)
extension.
