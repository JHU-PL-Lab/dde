(* https://github.com/adamsmd/paper-push-down-for-free-prototype/blob/master/benchmarks/gcfa2/mj09.scm *)

letassert x = (
  let h = fun b ->
    let g = (fun z -> z) in
    let f = (fun k -> if b then k 1 else k 2) in
    let y = (f (fun x -> x)) in
    (g y)
  in
  let x = (h true) in
  let y = (h false) in
  y
) in x = 2
