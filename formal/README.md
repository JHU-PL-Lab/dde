# DDE Formalizations

Current progress:
- [x] concrete lambda calculus opsem
- [ ] correctness properties of above
- [ ] other concrete opsems, e.g. environment/closure-based opsem
- [ ] equivalence among concrete opsems
- [ ] abstract opsems

## Set up

Follow the [official instructions](https://coq.inria.fr/download) to install Coq.

## Develop

```sh
make # to compile all modules
make MODULE.vo # to compile a specific module

coq_makefile -f _CoqProject *.v -o Makefile # to generate a new Makefile when adding new modules

coqc -Q . DDE MODULE.v # to use the Coq compiler directly
```

If you're using VSCode, I recommend installing the
[VSCoq](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq)
extension.
