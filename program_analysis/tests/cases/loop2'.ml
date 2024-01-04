let lp1 = fun self1 -> fun i ->
  if i = 0 then 5
  else
    let lp2 = fun self2 -> fun j ->
      if j = 0 then self1 self1 (i - 1) else self2 self2 (j - 1)
    in
    lp2 lp2 10 
in
lp1 lp1 10