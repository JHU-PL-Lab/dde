open Program_analysis.Lib
open Test_utils
open Ddeast

let set = Hashset.create 100

let rec is_closed e =
  match e with
  | Int _ | Bool _ -> true
  | Var (x, _) -> Hashset.mem set x
  | Let (id, e1, e2, _) ->
      is_closed e1
      &&
      let _ = Hashset.add set id in
      is_closed e2
  | Function (id, e, _) ->
      let _ = Hashset.add set id in
      is_closed e
  | Appl (e1, e2, _)
  | Plus (e1, e2, _)
  | Minus (e1, e2, _)
  | Equal (e1, e2, _)
  | And (e1, e2, _)
  | Or (e1, e2, _) ->
      is_closed e1 && is_closed e2
  | Not (e, _) -> is_closed e
  | If (e1, e2, e3, _) -> is_closed e1 && is_closed e2 && is_closed e3

let run () =
  Core.Quickcheck.test quickcheck_generator_expr ~sexp_of:sexp_of_expr
    ~trials:10000
    ~sizes:
      (Base.Sequence.cycle_list_exn (Core.List.range 0 20 ~stop:`inclusive))
    ~f:(fun e ->
      if is_closed e then
        e |> au
        (* |> Format.asprintf "%a" pp_expr *)
        |> print_endline;
      Hashset.clear set (*|> ignore*))

(*
  TODOs:
  - check number of |'s in output involving appls and lookups
  - check exception thrown
  - generated node labels are messed up
  - what does `size` mean for generating expr's
  - update with correct ids and use random existing vars in proogram
  - resolve programs with runtime type errors - smaller programs (~15 nodes)
  - papers on generating random programs
  - evaluate generated program and see if it falls in the range of the analysis
  - unevaluation (reverse evaluation, random test construction, random program synthesis) - reversing small-step semantics
*)