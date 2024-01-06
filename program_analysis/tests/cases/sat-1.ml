(* https://github.com/JHU-PL-Lab/odefa/blob/toplas/benchmark/cases/sat-1.scm *)

let phi = fun x1 -> fun x2 -> fun x3 -> fun x4 ->
  (x1 || (not x2) || (not x3)) &&
  ((not x2) || (not x3)) &&
  (x4 || x2) in

let try_ = fun f ->
  (f true) || (f false) in

let sat_solve_4 = fun p ->
  try_ (fun n1 ->
    try_ (fun n2 ->
      try_ (fun n3 ->
        try_ (fun n4 ->
          p n1 n2 n3 n4
        )
      )
    )
  ) in

sat_solve_4 phi