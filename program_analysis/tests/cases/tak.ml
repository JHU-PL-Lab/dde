(* https://github.com/adamsmd/paper-push-down-for-free-prototype/blob/master/benchmarks/larceny/tak.sch *)
(* letassert x = *)
  let tak = fun self -> fun x -> fun y -> fun z ->
    if not (y < x) then z
    else
      self self
        (self self (x - 1) y z)
        (self self (y - 1) z x)
        (self self (z - 1) x y)
  in
  tak tak 32 15 8
(* in x = 0 *)
