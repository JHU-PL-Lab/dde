open Program_analysis.Lib
open Utils
open Interpreter
module QC = Core.Quickcheck

let filter_simple (e : Ast.expr) =
  match e with Function _ | Int _ | Bool _ | Var _ -> None | _ -> Some e

let rec rename_vars ?(vars = IdentSet.empty) (e : Ast.expr) =
  match e with
  | Int _ | Bool _ -> e
  | Function (id, e, _) ->
      let vars = IdentSet.add id vars in
      Function (id, rename_vars ~vars e, fresh_label ())
  | Var (id, _) -> (
      match IdentSet.find_opt id vars with
      | Some _ -> Var (id, fresh_label ())
      | None -> (
          match IdentSet.choose_opt vars with
          | Some (Ident chosen_id) -> Var (Ident chosen_id, fresh_label ())
          | None -> Var (id, fresh_label ())))
  | Appl (e1, e2, _) ->
      Appl (rename_vars ~vars e1, rename_vars ~vars e2, fresh_label ())
  | If (e1, e2, e3, _) ->
      If
        ( rename_vars ~vars e1,
          rename_vars ~vars e2,
          rename_vars ~vars e3,
          fresh_label () )
  | Plus (e1, e2) -> Plus (rename_vars ~vars e1, rename_vars ~vars e2)
  | Minus (e1, e2) -> Minus (rename_vars ~vars e1, rename_vars ~vars e2)
  | Equal (e1, e2) -> Equal (rename_vars ~vars e1, rename_vars ~vars e2)
  | And (e1, e2) -> And (rename_vars ~vars e1, rename_vars ~vars e2)
  | Or (e1, e2) -> Or (rename_vars ~vars e1, rename_vars ~vars e2)
  | Not e -> Not (rename_vars ~vars e)
  | Let _ -> failwith "unreachable"

let fix_appl (e : Ast.expr) =
  match e with
  | Appl (e1, e2, _) -> (
      match e1 with
      | Function _ | Appl _ | If _ -> e1
      | _ ->
          let fun_gen =
            QC.Generator.filter Ast.quickcheck_generator_expr ~f:(function
              | Function _ | Appl _ | If _ | Var _ -> true
              | _ -> false)
          in
          QC.random_value fun_gen)
  | _ -> e

let rec strip_label_fb (e : Ast.expr) : Fbast.expr =
  match e with
  | Int i -> Int i
  | Bool b -> Bool b
  | Function (Ident x, e, _) -> Function (Ident x, strip_label_fb e)
  | Appl (e1, e2, _) -> Appl (strip_label_fb e1, strip_label_fb e2)
  | Var (Ident x, _) -> Var (Ident x)
  | Plus (e1, e2) -> Plus (strip_label_fb e1, strip_label_fb e2)
  | Minus (e1, e2) -> Minus (strip_label_fb e1, strip_label_fb e2)
  | Equal (e1, e2) -> Equal (strip_label_fb e1, strip_label_fb e2)
  | And (e1, e2) -> And (strip_label_fb e1, strip_label_fb e2)
  | Or (e1, e2) -> Or (strip_label_fb e1, strip_label_fb e2)
  | Not e -> Not (strip_label_fb e)
  | If (e1, e2, e3, _) ->
      If (strip_label_fb e1, strip_label_fb e2, strip_label_fb e3)
  | _ -> raise Unreachable

let run () =
  QC.test Ast.quickcheck_generator_expr
    ~sexp_of:(fun e -> e |> rename_vars |> Ast.sexp_of_expr)
    ~trials:1000
    ~sizes:(Base.Sequence.cycle_list_exn (Core.List.range 3 5 ~stop:`inclusive))
    ~seed:`Nondeterministic
    ~f:(fun e ->
      e |> filter_simple |>> rename_vars |>> fix_appl
      |> (fun e ->
           reset_label ();
           e)
      |>-> (fun e ->
             try
               (* run Fb interpreter to validate (closed + well-typed) *)
               let e' = strip_label_fb e in
               e' |> Fbinterp.eval |> ignore;
               Format.printf "Fb: %a\n" Fbpp.pp_expr e';
               Some e
             with _ -> None)
      |>> au
      (* |>> (fun e -> Format.asprintf "%a" pp_expr e) *)
      |>> (fun s -> Format.printf "PA:%s\n" s)
      |> ignore)

(*
  TODOs:
  - generate good programs in the first place v.s. correcting programs post-hoc
  - PA result superset of Fb
  - keep database of generated expression and use them as combinators
  - future: keep database of contexts (holes)
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
