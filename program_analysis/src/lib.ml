open Interpreter.Ast
open Base_quickcheck
open Sexplib.Std
open Core.Option.Let_syntax

exception Unreachable
exception Bad_type

type sigma_t = int list [@@deriving show { with_path = false }]

type op_result_value =
  | PlusOp of result_value * result_value
  | MinusOp of result_value * result_value
  | EqualOp of result_value * result_value
  | AndOp of result_value * result_value
  | OrOp of result_value * result_value
  | NotOp of result_value

and result_value =
  | OpResult of op_result_value
  | ChoiceResult of { choices : result_value list; l : int; sigma : sigma_t }
  | FunResult of { f : expr; l : int; sigma : sigma_t }
  | StubResult of { e : expr; sigma : sigma_t }
  | IntResult of int
  | BoolResult of bool
[@@deriving show { with_path = false }]

let prune_sigma ?(k = 2) sigma = List.filteri (fun i _ -> i < k) sigma

let rec contains_sigma sigma_parent sigma_child =
  match (sigma_parent, sigma_child) with
  | _, [] -> true
  | [], _ -> false
  | l_parent :: ls_parent, l_child :: ls_child ->
      l_parent = l_child && contains_sigma ls_parent ls_child

let rec fold_choices f choices acc =
  match choices with
  | ChoiceResult { choices = choices'; _ } :: rest ->
      fold_choices f (choices' @ rest) acc
  | res :: rest -> fold_choices f rest (f res acc)
  | [] -> acc

let s_set = Hashset.create 1000
let print_set () = Hashset.iter (fun x -> print_endline @@ show_sigma_t x) s_set

module VSet = Set.Make (struct
  type t = expr * sigma_t

  let compare (l1, sigma1) (l2, sigma2) =
    match compare l1 l2 with 0 -> compare sigma1 sigma2 | n -> n
end)

(* used to accumulate disjuncts when stitching stacks at Var Non-Local *)
module ChoiceSet = Set.Make (struct
  type t = result_value

  let compare = compare
end)

let pp_pair fmt (l, sigma) =
  Format.fprintf fmt "(%d, %s)" l @@ show_sigma_t sigma

let pp_pair_list fmt ls = Format.pp_print_list pp_pair fmt ls
let is_debug_mode = ref false

let all_combs l1 l2 =
  List.fold_left
    (fun acc x -> List.fold_left (fun acc y -> (x, y) :: acc) acc l2)
    [] l1

(* TODO: denote stub as any_num *)
(*? pretty hard to test ChoiceResult/StubResult because examples are few *)
let rec eval_int res =
  match res with
  | BoolResult _ | FunResult _ -> raise Bad_type
  | IntResult i -> [ i ]
  | OpResult op_res -> (
      match op_res with
      | PlusOp (i1, i2) ->
          let i1s = eval_int i1 in
          let i2s = eval_int i2 in
          List.map (fun (x, y) -> x + y) (all_combs i1s i2s)
      | MinusOp (i1, i2) ->
          let i1s = eval_int i1 in
          let i2s = eval_int i2 in
          (* TODO: dedup *)
          let a = List.map (fun (x, y) -> x - y) (all_combs i1s i2s) in
          (* List.iter (fun b -> Format.printf "%d, " b) a;
             Format.printf "\n"; *)
          a
      | _ -> raise Unreachable [@coverage off])
  | ChoiceResult { choices; _ } -> List.map eval_int choices |> List.concat
  | StubResult _ ->
      print_endline "int stub";
      []

and eval_bool res =
  match res with
  | IntResult _ | FunResult _ -> raise Bad_type
  | BoolResult b -> [ b ]
  | OpResult op_res -> (
      match op_res with
      | EqualOp (i1, i2) ->
          let i1s = eval_int i1 in
          let i2s = eval_int i2 in
          [ List.exists (fun x -> List.mem x i2s) i1s ]
      | AndOp (b1, b2) -> []
      | OrOp (b1, b2) -> []
      | NotOp b -> []
      | _ -> raise Unreachable [@coverage off])
  | ChoiceResult _ ->
      print_endline "bool choice";
      []
  | StubResult _ ->
      print_endline "bool stub";
      []

let rec analyze_aux expr sigma v_set =
  match expr with
  | Int i -> Some (IntResult i)
  | Bool b -> Some (BoolResult b)
  | Function (_, _, l) ->
      (* TODO: wrap all results in ChoiceResult *)
      Some
        (ChoiceResult
           { choices = [ FunResult { f = expr; l; sigma } ]; l; sigma })
  | Appl (e, _, l) -> (
      let l_app_sigma = prune_sigma (l :: sigma) in
      let vis_state = (expr, l_app_sigma) in
      (if !is_debug_mode then Format.printf "%d\n" l) [@coverage off];
      (* Application Stub *)
      if VSet.mem vis_state v_set then
        Some (StubResult { e = expr; sigma = l_app_sigma })
      else
        (* Application *)
        match%bind analyze_aux e sigma v_set with
        | ChoiceResult { choices; _ } ->
            let result_list =
              fold_choices
                (fun fun_res acc ->
                  match fun_res with
                  | FunResult { f = Function (_, e_i, _); _ } -> (
                      Hashset.add s_set (l :: sigma);
                      match
                        analyze_aux e_i l_app_sigma (VSet.add vis_state v_set)
                      with
                      | Some res_i -> res_i :: acc
                      | None -> acc)
                  | _ -> raise Unreachable [@coverage off])
                choices []
            in
            Some
              (ChoiceResult { choices = result_list; l; sigma = l_app_sigma })
        | _ -> raise Unreachable [@coverage off])
  | Var (Ident x, l) -> (
      match get_myfun l with
      | Function (Ident x1, _, l_myfun) ->
          if x = x1 then (
            (* Var Local *)
            (if !is_debug_mode then (
               Format.printf "%s, %d\n" x l;
               flush stdout;
               print_set ()))
            [@coverage off];
            if List.length sigma = 0 then (
              Format.printf "empty sigma_0\n";
              None)
            else
              let vis_state = (expr, sigma) in
              (* Var Local Stub *)
              if VSet.mem vis_state v_set then
                Some (StubResult { e = expr; sigma })
              else
                let sigma_hd, sigma_tl = (List.hd sigma, List.tl sigma) in
                let sigma_hd_expr = get_myexpr sigma_hd in
                match sigma_hd_expr with
                | Appl (_, e2, l') ->
                    let res_list =
                      (* enumerate all matching stacks in the set *)
                      Hashset.fold
                        (fun sigma_i acc ->
                          let sigma_i_hd, sigma_i_tl =
                            (List.hd sigma_i, List.tl sigma_i)
                          in
                          (* the fact that we can prune away "bad" stacks like this
                             makes DDE for program analysis superior *)
                          if
                            sigma_i_hd = l'
                            && contains_sigma sigma_i_tl sigma_tl
                          then
                            match
                              (* stitch the stack to gain more precision *)
                              analyze_aux e2 sigma_i_tl
                                (VSet.add vis_state v_set)
                            with
                            | Some r_i -> r_i :: acc
                            | None -> acc
                          else acc)
                        s_set []
                    in
                    Some (ChoiceResult { choices = res_list; l; sigma })
                | _ -> raise Unreachable [@coverage off])
          else (
            (if !is_debug_mode then (
               Format.printf "%s, %d\n" x l;
               flush stdout;
               print_endline @@ show_sigma_t sigma;
               print_set ()))
            [@coverage off];
            let sigma_hd, sigma_tl = (List.hd sigma, List.tl sigma) in
            let sigma_hd_expr = get_myexpr sigma_hd in
            match sigma_hd_expr with
            | Appl (e1, _, l2) ->
                let res_list =
                  (* enumerate all matching stacks in the set *)
                  Hashset.fold
                    (fun sigma_i set_acc ->
                      let sigma_i_hd, sigma_i_tl =
                        (List.hd sigma_i, List.tl sigma_i)
                      in
                      if sigma_i_hd = l2 && contains_sigma sigma_i_tl sigma_tl
                      then
                        match
                          (* stitch the stack to gain more precision *)
                          analyze_aux e1 sigma_i_tl v_set
                        with
                        | Some (ChoiceResult { choices; _ }) ->
                            ChoiceSet.union set_acc
                            @@ fold_choices
                                 (fun fun_res acc ->
                                   match fun_res with
                                   | FunResult
                                       {
                                         f = Function (Ident x1', _, l1);
                                         l = _;
                                         sigma = sigma_i;
                                       }
                                     when x1 = x1' && l_myfun = l1 -> (
                                       match
                                         analyze_aux
                                           (Var (Ident x, l1))
                                           sigma_i v_set
                                       with
                                       | Some res_i -> ChoiceSet.add res_i acc
                                       | None -> acc)
                                   | _ -> acc)
                                 choices set_acc
                        | _ -> raise Unreachable [@coverage off]
                      else set_acc)
                    s_set ChoiceSet.empty
                in
                Some
                  (ChoiceResult
                     { choices = ChoiceSet.elements res_list; l; sigma })
            | _ -> raise Unreachable [@coverage off])
      | _ -> raise Unreachable [@coverage off])
  | If (e, e_true, e_false, l) ->
      let%map res = analyze_aux e sigma v_set in
      (* Format.printf "%s" (show_result_value res); *)
      let bs = eval_bool res in
      (* List.iter (fun b -> Format.printf "%b, " b) bs;
         Format.printf "\n"; *)
      let res_list =
        List.map
          (fun b ->
            (* TODO: actually match Some/None *)
            if b then Option.get @@ analyze_aux e_true sigma v_set
            else Option.get @@ analyze_aux e_false sigma v_set)
          bs
      in
      ChoiceResult { choices = res_list; l; sigma }
  | Plus (e1, e2) | Minus (e1, e2) | Equal (e1, e2) | And (e1, e2) | Or (e1, e2)
    ->
      let%bind r1 = analyze_aux e1 sigma v_set in
      let%bind r2 = analyze_aux e2 sigma v_set in
      Some
        (OpResult
           (match expr with
           | Plus _ -> PlusOp (r1, r2)
           | Minus _ -> MinusOp (r1, r2)
           | Equal _ -> EqualOp (r1, r2)
           | And _ -> AndOp (r1, r2)
           | Or _ -> OrOp (r1, r2)
           | _ -> raise Unreachable [@coverage off]))
  | Not e ->
      let%bind r = analyze_aux e sigma v_set in
      Some (OpResult (NotOp r))
  | Let _ -> raise Unreachable [@coverage off]

let analyze ~debug e =
  is_debug_mode := debug;

  let e = transform_let e in
  build_myfun e None;
  let r = analyze_aux e [] VSet.empty in

  (if !is_debug_mode then (
     Format.printf "\n%s\n\n" @@ show_expr e;
     flush stdout;
     print_endline "****** Label Table ******";
     print_myexpr myexpr;
     print_endline "****** Label Table ******\n"))
  [@coverage off];

  Option.get r

(* TODO: multiple layers of ChoiceResult - improve output readability *)
