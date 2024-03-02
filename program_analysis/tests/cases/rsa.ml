(* https://github.com/JHU-PL-Lab/odefa/blob/toplas/benchmark/cases/rsa.scm *)
(* Modified to mock language features not available in our language, e.g., mod *)

let mod = fun a -> fun b -> 0 in
let div = (fun a -> fun b -> a) in
let extended_gcd = fun self -> fun a -> fun b ->
  if mod a b = 0 then ({ hd = 0; tl = 1 })
  else
    let pair = self self b (mod a b) in
    let x' = (pair.hd) in
    let y' = (pair.tl) in
    ({ hd = y'; tl = x' - y' * (div a b) })
in

let modulo_inverse = (fun a -> fun n ->
  let pair = (extended_gcd extended_gcd a n) in
  mod (pair.hd) n)
in

let totient = fun p -> fun q -> (p - 1) * (q - 1) in

let square = (fun x -> x * x) in

let modulo_power = (fun self -> fun base -> fun exp -> fun n ->
  if exp = 0 then 1
  else if mod exp 2 = 1 then
    mod (base * self self base (exp - 1) n) n
  else
    mod (square (self self base (div exp 2) n)) n)
in
let gcd = fun a -> fun b -> 1 in

let is_legal_public_exponent = fun e -> fun p -> fun q ->
  e > 1 && e < totient p q && gcd e (totient p q) = 1
in

let private_exponent = fun e -> fun p -> fun q ->
  if is_legal_public_exponent e p q then
    modulo_inverse e (totient p q)
  else (-1)
in

let encrypt = (fun m -> fun e -> fun n ->
  if m > n then (-1)
  else modulo_power modulo_power m e n)
in

let decrypt = (fun c -> fun d -> fun n -> modulo_power modulo_power c d n) in

let p = 41 in
let q = 47 in
let n = (p * q) in
let e = 7 in
let d = (private_exponent e p q) in
let plaintext = 42 in
let ciphertext = (encrypt plaintext e n) in
let decrypted_ciphertext = (decrypt ciphertext d n) in

plaintext = decrypted_ciphertext