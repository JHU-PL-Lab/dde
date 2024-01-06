(* https://github.com/adamsmd/paper-push-down-for-free-prototype/blob/master/benchmarks/gcfa2/kcfa3.scm *)

letassert x =
  (fun f1 ->
    let a = (f1 true) in
    f1 false) (fun x1 ->
      (fun f2 ->
        let b = (f2 true) in
        f2 false) (fun x2 ->
          (fun f3 ->
            let c = (f3 true) in
            f3 false) (fun x3 -> (fun z -> z x1 x2 x3) (fun y1 -> fun y2 -> fun y3 -> y1))))
in not x