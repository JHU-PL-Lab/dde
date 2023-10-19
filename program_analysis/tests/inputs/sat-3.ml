let not' = fun b -> if b then false else true in
let phi = fun ps -> 
  let x1 = (ps.x1) in
  let x2 = (ps.x2) in
  let x3 = (ps.x3) in
  let x4 = (ps.x4) in
  let x5 = (ps.x5) in
  let x6 = (ps.x6) in
  let x7 = (ps.x7) in
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
                p ({ x1 = n1; x2 = n2; x3 = n3; x4 = n4; x5 = n5; x6 = n6; x7 = n7 })))))))) in

sat_solve_7 phi
