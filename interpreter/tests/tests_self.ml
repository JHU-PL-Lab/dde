open OUnit2
open Utils

let assert_equal = assert_equal ~printer:Core.Fn.id

let test_laziness _ =
  assert_equal "{ x = 1 + 1; y = 1 + 1 }"
    (peu "{ x = 1 + 1; y = (fun z -> z + 1) 1 }");
  assert_equal "1" (peu "{ x = 1 }.x");
  assert_equal "1" (peu "{ label = if true then 1 else 0 }.label");
  assert_equal "fun y -> 7"
    (peu ~should_simplify:true
       "(fun x -> fun y -> x) ((fun z -> z + 1) (1 + 2 + 3))");
  assert_equal "fun y -> 1"
    (peu ~should_simplify:true "(fun x -> fun y -> x) (if true then 1 else 0)")

let test_memoization _ =
  (* assert_equal "" (peu ~should_simplify:true (Tests_subst.dde_fib 15)); *)
  assert_equal ""
    (peu ~should_simplify:false
       "let fib = (fun self -> fun n -> if n = 0 or n = 1 then n else self \
        self (n - 1) + self self (n - 2)) in fib fib 21")

let test_record _ =
  (* gives value at leftmost x *)
  assert_equal "1" (peu ~should_simplify:true "{ x = 1; y = 3; x = 2 }.x");
  assert_equal "{ counter = -98; cond = true }"
    (peu ~should_simplify:true
       "let data = { counter = 99; cond = false } in if data.cond then { \
        counter = data.counter + 1; cond = false } else { counter = 1 - \
        data.counter; cond = true }");
  assert_equal "1"
    (peu ~should_simplify:true
       "(fun r -> if green in r then r.green else if blue in r then r.blue \
        else r.red) ({ cyan = 10; blue = 1 })");
  (* lists *)
  (* TODO: more to come *)
  assert_equal "2"
    (peu ~should_simplify:true "{ hd = 1; tl = { hd = 2; tl = {} } }.tl.hd")

let test_letassert _ =
  assert_equal "2" (peu ~should_simplify:true "letassert x = 1 + 1 in x = 2")

let list_incr =
  "let incr = fun self -> fun ls -> { hd = ls.hd + 1; tl = if hd in ls.tl then \
   self self (ls.tl) else {} } in incr incr"

let incr_cell =
  "let incr = fun self -> fun ls -> fun n -> if n = 0 then ls else self self \
   ({ hd = ls.hd + 1; tl = {} }) (n - 1) in incr incr"

let test_record_rec _ =
  assert_equal
    "{ hd = 2; tl = { hd = 3; tl = { hd = 4; tl = { hd = 5; tl = {} } } } }"
    (peu ~should_simplify:true
       (list_incr
      ^ " ({ hd = 1; tl = { hd = 2; tl = { hd = 3; tl = { hd = 4; tl = {} } } \
         } })"));
  assert_equal "{ hd = 5; tl = {} }"
    (peu ~should_simplify:true (incr_cell ^ " ({ hd = 0; tl = {} }) 5"))

let test_misc _ =
  assert_equal ""
    (peu
       "let append = fun self -> fun x -> fun y ->\n\
       \  if not (hd in x) then y\n\
       \  else { hd = x.hd; tl = self self (x.tl) y }\n\
        in\n\n\
        let flatten = fun self -> fun x ->\n\
       \  if not (hd in x) then x\n\
       \  else if not (hd in x.hd) then self self (x.tl)\n\
       \  else if hd in (x.hd) then { hd = x.hd.hd; tl = self self (append \
        append (x.hd.tl) (x.tl)) }\n\
       \  else { hd = x.hd; tl = {} }\n\
        in\n\n\
        flatten flatten ({ hd = { hd = 1; tl = { hd = 2; tl = {} } }; tl = { \
        hd = 3; tl = { hd = 4; tl = { hd = 5; tl = {} } } } })")

let dde_self_tests =
  [
    (* "Memoization" >:: test_memoization; *)
    (* "Record rec" >:: test_record_rec; *)
    "Laziness" >:: test_laziness;
    "Record operations" >:: test_record;
    "letassert" >:: test_letassert;
    (* "Misc." >:: test_misc; *)
  ]

let dde_self = "DDE against self" >::: dde_self_tests
