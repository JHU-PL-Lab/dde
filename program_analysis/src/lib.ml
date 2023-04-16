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
  (* storing just the label instead of the whole expression works
     because stubbing only happens at Appl and only Var Nonlocal
     swaps labels *)
  | StubResult of { l : label_t; sigma : sigma_t }
  | IntResult of int
  | BoolResult of bool

let prune_sigma ?(k = 2) sigma = List.filteri (fun i _ -> i < k) sigma

let rec contains_sigma sigma_parent sigma_child =
  match (sigma_parent, sigma_child) with
  | _, [] -> true
  | [], _ -> false
  | l_parent :: ls_parent, l_child :: ls_child ->
      l_parent = l_child && contains_sigma ls_parent ls_child

let rec fold_choices f accum choices =
  match choices with
  | ChoiceResult { choices = choices'; _ } :: rest ->
      fold_choices f accum (choices' @ rest)
  | res :: rest -> fold_choices f (f res accum) rest
  | [] -> accum

let set : sigma_t Hashset.t = Hashset.create 100

module ProgramPoint = struct
  type t = label_t * sigma_t

  let compare (l1, sigma1) (l2, sigma2) =
    match compare l1 l2 with 0 -> compare sigma1 sigma2 | n -> n
end

module VisSet = Set.Make (ProgramPoint)

let pp_list fmt ls = List.iter (fun l -> Format.fprintf fmt "%d, " l) ls
let pp_pair fmt (l, sigma) = Format.fprintf fmt "(%d, [%a])" l pp_list sigma

let pp_pair_list fmt ls =
  List.iter (fun l -> Format.fprintf fmt "%a, " pp_pair l) ls

let rec analyze_aux e sigma vis =
  match e with
  | Int i -> IntResult i
  | Bool b -> BoolResult b
  | Function (_, _, l) ->
      (*? should ChoiceResult wrap all results? *)
      ChoiceResult { choices = [ FunResult { f = e; l; sigma } ]; l; sigma }
  | Appl (e', _, l) -> (
      let l_app_sigma = prune_sigma (l :: sigma) in
      let vis_state = (l, l_app_sigma) in
      (* Stub *)
      (* TODO: most likely failure *)
      (* Format.printf "%a\n" pp_pair vis_state;
         Format.printf "[%a]\n\n" pp_pair_list vis; *)
      if List.mem vis_state vis then StubResult { l; sigma = l_app_sigma }
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
                        analyze_aux e_i l_app_sigma (vis_state :: vis)
                      in
                      res_i :: accum
                  | _ -> failwith "funresult (appl)" [@coverage off])
                [] choices
            in
            ChoiceResult { choices = result_list; l; sigma = l_app_sigma }
        | _ -> failwith "choice (appl)" [@coverage off])
  | Var (Ident x, l) -> (
      (* print_endline x;
         List.iter (fun i -> Printf.printf "%d " i) sigma;
         print_endline ""; *)
      let sigma_hd, sigma_tl = (List.hd sigma, List.tl sigma) in
      let sigma_hd_expr = get_expr sigma_hd in
      match get_outer_scope l with
      | Function (Ident x1, _, l_myfun) -> (
          if x = x1 then
            (* Var Local *)
            match sigma_hd_expr with
            | Appl (_, e2, l') ->
                (* enumerate all matching stacks in the set *)
                let result_list =
                  Hashset.fold
                    (fun sigma_i accum ->
                      let sigma_i_hd, sigma_i_tl =
                        (List.hd sigma_i, List.tl sigma_i)
                      in
                      if sigma_i_hd = l' && contains_sigma sigma_i_tl sigma_tl
                      then analyze_aux e2 sigma_i_tl vis :: accum
                      else accum)
                    set []
                in
                ChoiceResult { choices = result_list; l; sigma }
            | _ -> failwith "appl (var local)" [@coverage off]
          else
            (* Var Non-Local *)
            match sigma_hd_expr with
            | Appl (e1, _, l2) -> (
                match analyze_aux e1 sigma_tl vis with
                | ChoiceResult { choices; _ } ->
                    let result_list =
                      fold_choices
                        (fun fun_res accum ->
                          match fun_res with
                          | FunResult
                              {
                                f = Function (Ident x1', _, l1);
                                l = _;
                                sigma = sigma_i;
                              }
                            when x1 = x1' && l_myfun = l1 ->
                              analyze_aux (Var (Ident x, l1)) sigma_i vis
                              :: accum
                          | _ -> accum)
                        [] choices
                    in
                    ChoiceResult { choices = result_list; l; sigma }
                | _ -> failwith "choice" [@coverage off])
            | _ -> failwith "appl" [@coverage off])
      | _ -> failwith "function" [@coverage off])
  | Plus (e1, e2) ->
      let r1 = analyze_aux e1 sigma vis in
      let r2 = analyze_aux e2 sigma vis in
      OpResult (PlusOp (r1, r2))
  | Minus (e1, e2) ->
      let r1 = analyze_aux e1 sigma vis in
      let r2 = analyze_aux e2 sigma vis in
      OpResult (MinusOp (r1, r2))
  | Equal (e1, e2) ->
      let r1 = analyze_aux e1 sigma vis in
      let r2 = analyze_aux e2 sigma vis in
      OpResult (EqualOp (r1, r2))
  | And (e1, e2) ->
      let r1 = analyze_aux e1 sigma vis in
      let r2 = analyze_aux e2 sigma vis in
      OpResult (AndOp (r1, r2))
  | Or (e1, e2) ->
      let r1 = analyze_aux e1 sigma vis in
      let r2 = analyze_aux e2 sigma vis in
      OpResult (OrOp (r1, r2))
  | Not e' ->
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
  analyze_aux e [] []

(* TODO: multiple layers of ChoiceResult - improve output readability *)
