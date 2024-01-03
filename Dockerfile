FROM ocaml/opam:debian-11-ocaml-4.14
WORKDIR /home/opam
RUN sudo ln -f /usr/bin/opam-2.1 /usr/bin/opam && opam init --reinit -ni
RUN sudo apt-get update && sudo apt-get install -y libgmp-dev python3
WORKDIR /home/opam/pure-demand
COPY --chown=opam . .
RUN opam install . --deps-only && \
  eval $(opam env) && \
  dune test program_analysis
# RUN opam --version
# RUN opam exec -- dune --version
# RUN opam exec -- dune exec -- program_analysis/tests/tests.exe --runtime
# CMD ["dune", "exec", "--", "program_analysis/tests/tests.exe", "--runtime"]
ENTRYPOINT [ "_build/default/program_analysis/tests/tests.exe" ]
# ENTRYPOINT [ "opam", "list", "core" ]
