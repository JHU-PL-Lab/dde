(* https://github.com/JHU-PL-Lab/odefa/blob/toplas/benchmark/cases/fact.scm *)

let fact = fun self -> fun n ->
  if n = 0 then 1 else n * self self (n - 1) in
fact fact 3;;
