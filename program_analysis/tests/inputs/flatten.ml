let append = fun self -> fun x -> fun y ->
  if not (hd in x) then y
  else { hd = x.hd; tl = self self (x.tl) y }
in

let flatten = fun self -> fun x ->
  (* if hd in x then x
  else if not (hd in x.hd) then self self (x.tl)
  else if hd in x.hd then { hd = x.hd.hd; tl = self self (append append (x.hd.tl) (x.tl)) }
  else { hd = x.hd; tl = {} } *)
  if hd in x then 
in

flatten flatten ({ hd = { hd = 1; tl = { hd = 2; tl = {} } }; tl = { hd = 3; tl = { hd = 4; tl = { hd = 5; tl = {} } } } })