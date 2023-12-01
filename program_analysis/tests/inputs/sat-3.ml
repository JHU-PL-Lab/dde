(* let not' = fun b -> if b then false else true in *)
let phi = fun ps -> 
  ((ps.x1) || (ps.x2)) &&
  ((ps.x1) || (not (ps.x2)) || (not (ps.x3))) &&
  ((ps.x3) || (ps.x4)) &&
  ((not (ps.x4)) || (ps.x1)) &&
  ((not (ps.x2)) || (not (ps.x3))) &&
  ((ps.x4) || (ps.x2)) in

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
                p ({ x1 = n1; x2 = n2; x3 = n3; x4 = n4; x5 = n5; x6 = n6; x7 = n7 })))))))) in

sat_solve_7 phi
