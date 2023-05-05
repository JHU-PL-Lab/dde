# DDE Formalizations

Current progress:
- [ ] concrete operational semantics
  - [x] lambda calculus
    - [x] deterministic
  - [ ] environment/closure-based operational semantics
  - [ ] equivalence among concrete operational semantics
- [ ] abstract operational semantics
  - [x] non-deterministic lambda calculus
    - [ ] non-determinism
  - [ ] all-paths program analysis
  - [ ] equivalence among abstract opertional semantics

## Set up

Follow the [official instructions](https://coq.inria.fr/download) to install Coq.

## Develop

`dune build`, then use your preferred IDE to step through the scripts.

If you're using VSCode, I recommend installing the
[VSCoq](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq)
extension.
