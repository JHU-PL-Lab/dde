(* https://github.com/adamsmd/paper-push-down-for-free-prototype/blob/master/benchmarks/gcfa2/loop2.scm *)
letassert x =
  let lp1 = fun self1 -> fun i -> fun x ->
    if 0 = i then x
    else
      let lp2 = fun self2 -> fun j -> fun f -> fun y ->
        if 0 = j then self1 self1 (i - 1) y else self2 self2 (j - 1) f (f y)
      in
      lp2 lp2 10 (fun n -> n + i) x
  in
  lp1 lp1 10 0
in x >= 0
