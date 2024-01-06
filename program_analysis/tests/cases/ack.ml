(* https://github.com/adamsmd/paper-push-down-for-free-prototype/blob/master/benchmarks/larceny/ack.sch *)

let ack = fun self -> fun m -> fun n ->
  if m = 0 then n + 1
  else if n = 0 then self self (m - 1) 1
  else self self (m - 1) (self self m (n - 1))
in
ack ack 3 12
