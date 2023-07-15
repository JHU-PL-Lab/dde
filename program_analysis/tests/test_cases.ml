open Program_analysis.Solver

let ri = zconst "r" isort
let rb = zconst "r" bsort

type test_case = {
  prog : string;
  verif : Z3.FuncDecl.func_decl -> Z3.Expr.expr;
}

let basic =
  [|
    {
      prog = "(fun x -> x) 1";
      verif = (fun p -> [ ri ] |. (p <-- [ ri ]) --> (ri === zint 1));
    };
    {
      prog = "(fun y -> 1 + y) 2";
      verif = (fun p -> [ ri ] |. (p <-- [ ri ]) --> (ri === zint 3));
    };
  |]

let nonlocal_lookup =
  [|
    {
      prog = "(fun x -> (fun y -> x + y) 2) 1";
      verif = (fun p -> [ ri ] |. (p <-- [ ri ]) --> (ri === zint 3));
    };
    {
      prog = "((fun x -> fun y -> x + y) 1) 2";
      verif = (fun p -> [ ri ] |. (p <-- [ ri ]) --> (ri === zint 3));
    };
    {
      prog = "(fun x -> (fun y -> (fun z -> x + y + z) 2) 1) 3";
      verif = (fun p -> [ ri ] |. (p <-- [ ri ]) --> (ri === zint 6));
    };
  |]

let local_stitching =
  [|
    {
      prog =
        "let add = (fun num -> fun n -> n + num) in\n\
         let add1 = add 1 in\n\
         let add1' = (fun n -> add1 n) in\n\
         add1 1 + add1' 1";
      verif = (fun p -> [ ri ] |. (p <-- [ ri ]) --> (ri === zint 4));
    };
    {
      prog =
        "let add = (fun f -> fun g -> fun x -> f g x) in\n\
         let add1 = add (fun z -> fun n -> z n + 2) in\n\
         let add2 = add1 (fun y -> y + 1) in\n\
         add2 0";
      verif = (fun p -> [ ri ] |. (p <-- [ ri ]) --> (ri === zint 3));
    };
  |]

(* TODO: nested ifs *)
let conditional =
  [|
    {
      prog = "(fun id -> id 10) (fun n -> if n = 0 then 0 else 1 + (n - 1))";
      verif = (fun p -> [ ri ] |. (p <-- [ ri ]) --> (ri === zint 10));
    };
    {
      prog = "if true then 1 else 2";
      verif = (fun p -> [ ri ] |. (p <-- [ ri ]) --> (ri === zint 1));
    };
    {
      prog = "(fun x -> (if true then (fun y -> y) else (fun z -> z)) x) 1";
      verif = (fun p -> [ ri ] |. (p <-- [ ri ]) --> (ri === zint 1));
    };
  |]

let currying =
  [|
    {
      prog =
        "let add = (fun num -> fun n -> n + num) in let add1 = add 1 in add1 2";
      verif = (fun p -> [ ri ] |. (p <-- [ ri ]) --> (ri === zint 3));
    };
    {
      prog =
        "(fun add -> (fun add1 -> (fun add2 -> add1 2) (add 2)) (add 1)) (fun \
         num -> fun n -> n + num)";
      verif = (fun p -> [ ri ] |. (p <-- [ ri ]) --> (ri === zint 3));
    };
    {
      prog =
        "let add = (fun num -> fun n -> n + num) in let add2 = add 2 in add2 1";
      verif = (fun p -> [ ri ] |. (p <-- [ ri ]) --> (ri === zint 3));
    };
    {
      prog =
        "let add = (fun num -> fun n -> n + num) in let add1 = add 1 in let \
         add2 = add 2 in add1 2 + add2 1";
      verif = (fun p -> [ ri ] |. (p <-- [ ri ]) --> (ri === zint 6));
    };
    {
      prog =
        "let add = (fun num -> fun n -> n + num) in\n\
         let add1 = add 1 in\n\
         let add2 = add 2 in\n\
         let add3 = add 3 in\n\
         let add4 = add 4 in\n\
         let add5 = add 5 in\n\
         add1 1 + add2 1 + add3 1 + add4 1 + add5 1";
      verif = (fun p -> [ ri ] |. (p <-- [ ri ]) --> (ri === zint 20));
    };
  |]

let recursion =
  [|
    {
      prog =
        "let id = fun self -> fun n -> if n = 0 then 0 else 1 + self self (n - \
         1) in id id 10";
      verif = (fun p -> [ ri ] |. (p <-- [ ri ]) --> (ri >== zint 0));
    };
  |]
