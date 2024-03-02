(* https://github.com/JHU-PL-Lab/odefa/blob/toplas/benchmark/cases/map.scm *)

let id = (fun xx -> xx) in
let my_map =
  (fun f -> fun l ->
    let lp = fun self -> fun lst ->
      if not (hd in lst) then {}
      else { hd = id f (lst.hd); tl = self self (lst.tl) }
    in
    lp lp l)
in
let _ = my_map (id (fun b -> 1 + b)) ({ hd = 1; tl = { hd = 2; tl = { hd = 3; tl = {} } } }) in
my_map (id (fun b -> 1 + b)) ({ hd = 7; tl = { hd = 8; tl = { hd = 9; tl = {} } } })
(* my_map (id (fun b -> 1 + b)) ({ hd = 7; tl = { hd = 8; tl = { hd = 9; tl = { hd = 10; tl = {} } } } }) *)