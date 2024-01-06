(* https://github.com/JHU-PL-Lab/odefa/blob/toplas/benchmark/cases/cpstak.scm *)

let cpstak = fun x -> fun y -> fun z ->
  let tak = fun self -> fun x -> fun y -> fun z -> fun k ->
    if not (y < x) then k z
    else
      self self (x - 1) y z (fun v1 ->
          self self (y - 1) z x (fun v2 ->
              self self (z - 1) x y (fun v3 -> self self v1 v2 v3 k)))
  in
  tak tak x y z (fun a -> a)
in
cpstak 32 15 18
