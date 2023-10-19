(* https://github.com/JHU-PL-Lab/odefa/blob/toplas/benchmark/cases/sat-3.scm *)

let phi = fun x1 -> fun x2 -> fun x3 -> fun x4 -> fun x5 -> fun x6 -> fun x7 ->
  (x1 || x2) &&
  (x1 || (if x2 then false else true) || (if x3 then false else true)) &&
  (x3 || x4) &&
  ((if x4 then false else true) || x1) &&
  ((if x2 then false else true) || (if x3 then false else true)) &&
  (x4 || x2) in

let try_ = fun f ->
  f true || f false in

let sat_solve_7 = fun p ->
  try_ (fun n1 ->
    try_ (fun n2 ->
      try_ (fun n3 ->
        try_ (fun n4 ->
          try_ (fun n5 ->
            try_ (fun n6 ->
              try_ (fun n7 ->
                p n1 n2 n3 n4 n5 n6 n7))))))) in

sat_solve_7 phi
