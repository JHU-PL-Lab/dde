FROM ocaml/opam:debian-11-ocaml-4.14
WORKDIR /home/opam
RUN sudo ln -f /usr/bin/opam-2.1 /usr/bin/opam && opam init --reinit -ni
RUN sudo apt-get update && sudo apt-get install -y libgmp-dev python3
WORKDIR /home/opam/pure-demand
COPY --chown=opam . .
RUN opam install -y --deps-only . && \
  eval $(opam env) && \
  opam exec -- dune test program_analysis
ENTRYPOINT [ "_build/default/program_analysis/tests/tests.exe" ]
