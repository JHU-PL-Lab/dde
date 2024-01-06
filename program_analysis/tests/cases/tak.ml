(* https://github.com/JHU-PL-Lab/odefa/blob/toplas/benchmark/cases/tak.scm *)

let tak = fun self -> fun x -> fun y -> fun z ->
  if not (y < x) then z
  else
    self self
      (self self (x - 1) y z)
      (self self (y - 1) z x)
      (self self (z - 1) x y)
in
tak tak 32 15 8
