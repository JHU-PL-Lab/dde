let lp1 = fun self1 -> fun i ->
  if i = 0 then 5
  else
    self1 self1 (i - 1) 
in
lp1 lp1 10