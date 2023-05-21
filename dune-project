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
  "Formally verified concrete and abstract interpretation based on DDE"))
