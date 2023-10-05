let rec extended_gcd a b =
  if a mod b = 0 then
    (0, 1)
  else
    let x, y = extended_gcd b (a mod b) in
    let x' = fst (x, y) in
    let y' = snd (x, y) in
    (y', x' - y' * (a / b))