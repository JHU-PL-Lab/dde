open Program_analysis.Lib
open Test_utils
open Ddeast
module QC = Core.Quickcheck

module IdentSet = Set.Make (struct
  type t = ident

  let compare ident1 ident2 =
    match (ident1, ident2) with Ident id1, Ident id2 -> compare id1 id2
end)

let label = ref (-1)

let fresh_label () =
  label := !label + 1;
  !label

let reset_label () = label := -1

let rec rename_vars ?(vars = IdentSet.empty) (e : expr) =
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
  | Plus (e1, e2, _) ->
      Plus (rename_vars ~vars e1, rename_vars ~vars e2, fresh_label ())
  | Minus (e1, e2, _) ->
      Minus (rename_vars ~vars e1, rename_vars ~vars e2, fresh_label ())
  | Equal (e1, e2, _) ->
      Equal (rename_vars ~vars e1, rename_vars ~vars e2, fresh_label ())
  | And (e1, e2, _) ->
      And (rename_vars ~vars e1, rename_vars ~vars e2, fresh_label ())
  | Or (e1, e2, _) ->
      Or (rename_vars ~vars e1, rename_vars ~vars e2, fresh_label ())
  | Not (e, _) -> Not (rename_vars ~vars e, fresh_label ())
  | Let _ -> failwith "unreachable"

let ( |>% ) v f = Option.map f v

let rec strip_label_fb (e : Ddeast.expr) : Fbast.expr =
  match e with
  | Int i -> Int i
  | Bool b -> Bool b
  | Function (Ident x, e, _) -> Function (Ident x, strip_label_fb e)
  | Appl (e1, e2, _) -> Appl (strip_label_fb e1, strip_label_fb e2)
  | Var (Ident x, _) -> Var (Ident x)
  | Plus (e1, e2, _) -> Plus (strip_label_fb e1, strip_label_fb e2)
  | Minus (e1, e2, _) -> Minus (strip_label_fb e1, strip_label_fb e2)
  | Equal (e1, e2, _) -> Equal (strip_label_fb e1, strip_label_fb e2)
  | And (e1, e2, _) -> And (strip_label_fb e1, strip_label_fb e2)
  | Or (e1, e2, _) -> Or (strip_label_fb e1, strip_label_fb e2)
  | Not (e, _) -> Not (strip_label_fb e)
  | If (e1, e2, e3, _) ->
      If (strip_label_fb e1, strip_label_fb e2, strip_label_fb e3)
  | _ -> raise Unreachable

let run () =
  QC.test quickcheck_generator_expr (* ~sexp_of:sexp_of_expr *)
    ~sexp_of:(fun e -> e |> rename_vars |> sexp_of_expr)
    ~trials:1000
    ~sizes:(Base.Sequence.cycle_list_exn (Core.List.range 3 5 ~stop:`inclusive))
    ~seed:`Nondeterministic
    ~f:(fun e ->
      e |> rename_vars
      |> (fun e ->
           reset_label ();
           e)
      |> (fun e ->
           try
             (* run Fb interpreter to validate (closed + well-typed) *)
             let e' = strip_label_fb e in
             e' |> Fbinterp.eval |> ignore;
             Format.printf "Fb: %a\n" Fbpp.pp_expr e';
             Some e
           with _ -> None)
      |>% au
      (* |>% (fun e -> Format.asprintf "%a" pp_expr e) *)
      |>% (fun s -> Format.printf "PA:%s\n" s)
      |> ignore)

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