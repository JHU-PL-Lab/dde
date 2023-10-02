(* (define (println s)
  (display s)
  (newline))

(define (phi x1 x2 x3 x4)
  (and (or x1 (not x2) (not x3))
       (or (not x2) (not x3))
       (or x4 x2)))

(define (try f)
  (println "trying")
  (or (f #t) (f #f)))

(define (sat-solve-4 p)
  (try (lambda (n1)
         (try (lambda (n2)
                (try (lambda (n3)
                       (try (lambda (n4)
                              (p n1 n2 n3 n4))))))))))

                        
(display (sat-solve-4 phi))
(newline) *)

letassert x =
let phi = fun x1 -> fun x2 -> fun x3 -> fun x4 ->
  (x1 or (not x2) or (not x3)) and
  ((not x2) or (not x3)) and
  (x4 or x2) in

let try_ = fun f ->
  (f true) or (f false) in

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
in x