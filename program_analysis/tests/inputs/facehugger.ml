let id = (fun x -> x) in
let f = fun self -> fun n ->
  if n <= 1 then 1
  else n * (self self (n - 1)) in
let g = fun self -> fun n ->
  if n <= 1 then 1
  else n * (self self (n - 1)) in
((id f) (id f) 3) + ((id g) (id g) 4)