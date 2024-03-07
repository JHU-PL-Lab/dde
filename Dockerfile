FROM ocaml/opam:ubuntu-23.04-ocaml-4.14

RUN sudo apt-get update && sudo apt-get install -y libgmp-dev python3 vim emacs graphviz
WORKDIR /home/opam
RUN sudo ln -f /usr/bin/opam-2.1 /usr/bin/opam && opam init --reinit -ni
RUN echo "eval $(opam env)" >> .bashrc

WORKDIR /home/opam/pure-demand
COPY --chown=opam . .
RUN opam install core.v0.15.1 core_unix.v0.15.2 core_bench.v0.15.0 dune.3.7.1 menhir.20220210 ounit2.2.2.7 utop.2.11.0 fmt.0.9.0 logs.0.7.0 ppx_let.v0.15.0 ppx_deriving.5.2.1 ppx_jane.v0.15.0 landmarks.1.4 landmarks-ppx.1.4 && eval $(opam env)
RUN opam install z3.4.12.2-1 && eval $(opam env)

RUN opam exec -- dune build

ENTRYPOINT [ "/bin/bash" ]
