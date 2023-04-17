open Interpreter.Ast
open Base_quickcheck
open Sexplib.Std

exception Unreachable

type label_t = int
type sigma_t = label_t list

type op_result_value =
  | PlusOp of result_value * result_value
  | MinusOp of result_value * result_value
  | EqualOp of result_value * result_value
  | AndOp of result_value * result_value
  | OrOp of result_value * result_value
  | NotOp of result_value

and result_value =
  | OpResult of op_result_value
  | ChoiceResult of {
      choices : result_value list;
      l : label_t;
      sigma : sigma_t;
    }
  | FunResult of { f : expr; l : label_t; sigma : sigma_t }
  (* TODO: don't store the entire expression *)
  | StubResult of { e : expr; sigma : sigma_t }
  | IntResult of int
  | BoolResult of bool

let prune_sigma ?(k = 2) sigma = List.filteri (fun i _ -> i < k) sigma

let rec contains_sigma sigma_parent sigma_child =
  match (sigma_parent, sigma_child) with
  | _, [] -> true
  | [], _ -> false
  | l_child :: ls_child, l_parent :: ls_parent ->
      l_child = l_parent && contains_sigma ls_parent ls_child

let rec fold_choices f accum choices =
  match choices with
  | ChoiceResult { choices = choices'; _ } :: rest ->
      fold_choices f accum (choices' @ rest)
  | res :: rest -> fold_choices f (f res accum) rest
  | [] -> accum

let set : sigma_t Hashset.t = Hashset.create 100
(* let vis : (expr * sigma_t) Hashset.t = Hashset.create 50 *)

module ProgramPoint = struct
  type t = expr * sigma_t

  let compare (e1, sigma1) (e2, sigma2) =
    match compare e1 e2 with 0 -> compare sigma1 sigma2 | n -> n
end

module VisSet = Set.Make (ProgramPoint)

let rec analyze_aux e sigma vis =
  match e with
  | Int i -> IntResult i
  | Bool b -> BoolResult b
  | Function (_, _, l) ->
      (*? should ChoiceResult wrap all results? *)
      ChoiceResult { choices = [ FunResult { f = e; l; sigma } ]; l; sigma }
  | Appl (e', _, l) -> (
      let sigma_app_l = prune_sigma (l :: sigma) in
      (* Stub *)
      if VisSet.mem (e, sigma_app_l) vis then
        StubResult { e; sigma = sigma_app_l }
      else
        (* Application *)
        match analyze_aux e' sigma vis with
        | ChoiceResult { choices; _ } ->
            let result_list =
              fold_choices
                (fun fun_res accum ->
                  match fun_res with
                  | FunResult { f = Function (_, e_i, _); _ } ->
                      Hashset.add set (l :: sigma);
                      let res_i =
                        analyze_aux e_i sigma_app_l
                          (VisSet.add (e, sigma_app_l) vis)
                      in
                      res_i :: accum
                  | _ -> failwith "funresult (appl)" [@coverage off])
                [] choices
            in
            ChoiceResult { choices = result_list; l; sigma = sigma_app_l }
        | _ -> failwith "choice (appl)" [@coverage off])
  | Var (Ident x, l) -> (
      (* print_endline "before"; *)
      let sigma_hd = List.hd sigma in
      (* print_endline "after"; *)
      let sigma_tl = List.tl sigma in
      match get_outer_scope l with
      | Function (Ident x1, _, _) -> (
          if x = x1 then
            (* Var Local *)
            match get_expr sigma_hd with
            | Appl (_, e2, l') ->
                (* enumerate all matching stacks in the set *)
                let result_list =
                  Hashset.fold
                    (fun sigma_i accum ->
                      if
                        List.hd sigma_i = l'
                        && contains_sigma (List.tl sigma_i) sigma_tl
                      then analyze_aux e2 (List.tl sigma_i) vis :: accum
                      else accum)
                    set []
                in
                ChoiceResult { choices = result_list; l; sigma }
            | _ -> failwith "appl (var local)" [@coverage off]
          else
            (* Var Non-Local *)
            match get_expr sigma_hd with
            | Appl (e1, _, l2) -> (
                match analyze_aux e1 sigma_tl vis with
                | ChoiceResult { choices; _ } ->
                    let result_list =
                      fold_choices
                        (fun fun_res accum ->
                          match fun_res with
                          | FunResult
                              {
                                f = Function (Ident x1, _, _);
                                l = l1;
                                sigma = sigma_i;
                              }
                            when x <> x1 ->
                              analyze_aux (Var (Ident x, l1)) sigma_i vis
                              :: accum
                          | _ -> accum)
                        [] choices
                    in
                    ChoiceResult { choices = result_list; l; sigma }
                | _ -> failwith "choice" [@coverage off])
            | _ -> failwith "appl" [@coverage off])
      | _ -> failwith "function" [@coverage off])
  | Plus (e1, e2, _) ->
      (* hereafter we use short forms `r1` (`res1`), `s2` (`set2`), etc.
         as code is clearer here and thus they are less ambiguous. *)
      let r1 = analyze_aux e1 sigma vis in
      let r2 = analyze_aux e2 sigma vis in
      OpResult (PlusOp (r1, r2))
  | Minus (e1, e2, _) ->
      let r1 = analyze_aux e1 sigma vis in
      let r2 = analyze_aux e2 sigma vis in
      OpResult (MinusOp (r1, r2))
  | Equal (e1, e2, _) ->
      let r1 = analyze_aux e1 sigma vis in
      let r2 = analyze_aux e2 sigma vis in
      OpResult (EqualOp (r1, r2))
  | And (e1, e2, _) ->
      let r1 = analyze_aux e1 sigma vis in
      let r2 = analyze_aux e2 sigma vis in
      OpResult (AndOp (r1, r2))
  | Or (e1, e2, _) ->
      let r1 = analyze_aux e1 sigma vis in
      let r2 = analyze_aux e2 sigma vis in
      OpResult (OrOp (r1, r2))
  | Not (e', _) ->
      let r = analyze_aux e' sigma vis in
      OpResult (NotOp r)
  | If (e', e1, e2, l) ->
      let _r = analyze_aux e' sigma vis in
      (* TODO: eval r *)
      (* on stub, denote as `anynum` *)
      let r_true = analyze_aux e1 sigma vis in
      let r_false = analyze_aux e2 sigma vis in
      ChoiceResult { choices = [ r_true; r_false ]; l; sigma }
  | Let _ -> raise Unreachable [@coverage off]

let analyze e =
  let e = transform_let e in
  fill_my_fun e None;
  analyze_aux e [] VisSet.empty

(* TODO: multiple layers of ChoiceResult - improve output readability *)
