(* https://github.com/JHU-PL-Lab/odefa/blob/toplas/benchmark/cases/eta.scm *)

letassert x =
let do_something = fun _ -> 10 in
let id = (fun y ->
  let _ = do_something (-1) in
  y) in

let _ = (id (fun a -> a)) true in
(id (fun b -> b)) false
in not x
