(lang dune 3.7)

(name dde)

(using menhir 2.1)

(using coq 0.7)

(generate_opam_files true)

(authors "JHU PL Lab <scott@cs.jhu.edu>")

(maintainers "JHU PL Lab <scott@cs.jhu.edu>")

(source
 (github JHU-PL-Lab/dde))

(package
 (name dde)
 (synopsis "Demand-Driven Execution (DDE)")
 (description
  "Formally verified concrete and abstract interpretation based on DDE")
 (depends
  (ocaml
   (>= 4.14.1))
  (coq
   (>= 8.17.0))
  (dune
   (>= 3.7))
  (ounit2
   (>= 2.2.7))
  (core
   (>= 0.15.1))
  (bisect_ppx
   (>= 2.8.1))
  (ppx_let
   (>= 0.15.0))
  (ppx_deriving
   (>= 5.2.1))
  (ppx_jane
   (>= 0.15.0))
  (utop
   (>= 2.11.0))
  (core_bench
   (>= 0.15.0))
  (core_unix
   (>= 0.15.2))
  (hashset
   (>= 1.0.0))))
