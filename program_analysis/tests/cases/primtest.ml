let square = fun x -> (x * x) in
let mod' = fun x -> fun y -> 0 in
let div = (fun x -> fun y -> x) in
let ceil = (fun x -> x) in
let log = (fun x -> x) in
let rand = (fun x -> x) in

let modulo_power = (fun self -> fun base -> fun exp -> fun n ->
  if exp = 0 then 1
  else if (mod' exp 2) = 1 then
    mod' (base * (self self base (exp - 1) n)) n
  else
    let temp = self self base (div exp 2) n in
    mod' (square temp) n)
  in

let is_trivial_composite = fun n ->
  mod' n 2 = 0 || mod' n 3 = 0 || mod' n 5 = 0 || mod' n 7 = 0 ||
  mod' n 11 = 0 || mod' n 13 = 0 || mod' n 17 = 0 || mod' n 19 = 0 ||
  mod' n 23 = 0
in

let is_fermat_prime = fun self -> fun n -> fun iterations ->
  (iterations <= 0) ||
  (let byte_size = ceil (div (log n) (log 2)) in
  let a = rand byte_size in
  if (modulo_power modulo_power a (n - 1) n) = 1 then
    self self n (iterations - 1)
  else false)
in

let generate_fermat_prime = (fun self -> fun byte_size -> fun iterations ->
  let n = rand byte_size in
  (* if (if (is_trivial_composite n) && (is_fermat_prime is_fermat_prime n iterations) then false else true) then *)
  if not ((is_trivial_composite n) && (is_fermat_prime is_fermat_prime n iterations)) then
    n
  else
    self self byte_size iterations)
in

let iterations = 10 in
let byte_size = 15 in
let result = (generate_fermat_prime generate_fermat_prime byte_size iterations) in
result