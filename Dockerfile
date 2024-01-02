FROM ocaml/opam:debian-11-ocaml-4.14
RUN sudo apt-get update && sudo apt-get install -y libgmp-dev python3
# z3
WORKDIR /home/opam
RUN sudo ln -f /usr/bin/opam-dev /usr/bin/opam && \
  opam init --reinit -ni
# eval $(opam env) && \
# opam install zarith ocamlfind && \
# git clone --depth 1 https://github.com/Z3Prover/z3.git && \
# cd z3 && \
# opam exec -- python3 scripts/mk_make.py --ml && \
# cd build && \
# opam exec -- make && \
# opam exec -- sudo make install
WORKDIR /home/opam/pure-demand
COPY --chown=opam . .
RUN opam install . --deps-only && \
  # opam install dune core && \
  # opam list core
  eval $(opam env) && \
  opam exec -- dune test program_analysis
# RUN opam --version
# RUN opam exec -- dune --version
# RUN opam exec -- dune exec -- program_analysis/tests/tests.exe --runtime
# CMD ["dune", "exec", "--", "program_analysis/tests/tests.exe", "--runtime"]
ENTRYPOINT [ "_build/default/program_analysis/tests/tests.exe" ]
