(* https://github.com/adamsmd/paper-push-down-for-free-prototype/blob/master/benchmarks/gcfa2/kcfa2.scm *)

letassert x =
  (fun f1 ->
    let a = (f1 true) in
    f1 false) (fun x1 ->
      (fun f2 ->
        let b = (f2 true) in
        let c = (f2 false) in
        f2 true) (fun x2 -> (fun z -> z x1 x2) (fun y1 -> fun y2 -> y1)))
in not x
