let mack = fun self -> fun n ->
  if n = 0 then self self 1
  else self self (self self (n - 1))
in
mack mack 0