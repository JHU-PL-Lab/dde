(* https://github.com/JHU-PL-Lab/odefa/blob/toplas/benchmark/cases/church.scm *)

let plus = (fun p1 ->
  let inner1 = (fun p2 ->
    let inner2 = (fun pf ->
      let inner3 = fun x -> (p1 pf) ((p2 pf) x) in
      inner3)
    in
    inner2)
  in
  inner1) in

let mult = (fun m1 ->
  let inner1 = (fun m2 ->
    let inner2 = fun mf -> m2 (m1 mf) in
    inner2)
  in
  inner1) in

let pred = (fun n ->
  let inner1 = (fun rf ->
    let inner2 = fun rx ->
      (((n (fun g -> fun h -> h (g rf))))
        (fun ignored -> rx))
       (fun id -> id)
    in
    inner2)
  in
  inner1) in

let sub = (fun s1 ->
  let inner1 = (fun s2 ->
    (s2 pred) s1)
  in
  inner1) in

let church0 = (fun f0 -> fun x0 -> x0) in
let church1 = (fun f1 -> fun x1 -> f1 x1) in
let church2 = (fun f2 -> fun x2 -> f2 (f2 x2)) in
let church3 = (fun f3 -> fun x3 -> f3 (f3 (f3 x3))) in

let church0' = fun z -> (z (fun zx -> false)) true in

let church' = fun self -> fun e1 -> fun e2 ->
  if church0' e1 then
    church0' e2
  else if church0' e2 then
    false
  else
    ((self self ((sub e1) church1)) ((sub e2) church1)) in

(church' church' ((mult church2) ((plus church1) church3)))
 ((plus ((mult church2) church1)) ((mult church2) church3))