(* https://github.com/adamsmd/paper-push-down-for-free-prototype/blob/master/benchmarks/gcfa2/blur.scm *)
letassert x =
  let id = (fun x -> x) in
  let blur = (fun y -> y) in
  let lp = fun self -> fun a -> fun n ->
    if n <= 1 then id a
    else
      let r = blur id true in
      let s = blur id false in
      not (blur (self self) s (n - 1))
  in
  lp lp false 2
in x
