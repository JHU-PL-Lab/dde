(lang dune 3.7)

(name dde)

(using menhir 2.1)

(using coq 0.7)

(authors "Anonymous")

(maintainers "Anonymous")

(package
 (name dde)
 (synopsis "Pure Demand Operational Semantics")
 (description
  "A novel minimal-state operational semantics for higher-order functional languages")
 (depends
  (ocaml
   (>= 4.14.1))
  (dune
   (>= 3.7.1))
  (menhir
   (>= 20220210))
  (ounit2
   (>= 2.2.7))
  (core
   (= 0.15.1))
  (core_unix
   (= 0.15.2))
  (core_bench
   (= 0.15.0))
  (ppx_let
   (>= 0.15.0))
  (ppx_deriving
   (>= 5.2.1))
  (ppx_jane
   (>= 0.15.0))
  (utop
   (>= 2.11.0))
  (fmt
   (>= 0.9.0))
  (logs
   (>= 0.7.0))
  (z3
   (>= 4.12.2-1))
  (landmarks
   (>= 1.4))
  (landmarks-ppx
   (>= 1.4))))
