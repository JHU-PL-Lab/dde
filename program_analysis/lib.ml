open Ddeast

exception Unreachable

type label_t = int [@@deriving show { with_path = false }]
type sigma_t = label_t list [@@deriving show { with_path = false }]
type set_t = sigma_t list
type vis_t = (sigma_t * expr) list

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
[@@deriving show { with_path = false }]

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

(* TODO: use hashset for S *)
let rec analyze_aux e sigma set vis =
  match e with
  | Int i -> (IntResult i, set)
  | Bool b -> (BoolResult b, set)
  | Function (_, _, l) ->
      (*? should ChoiceResult wrap all results? *)
      ( ChoiceResult { choices = [ FunResult { f = e; l; sigma } ]; l; sigma },
        set )
  | Appl (e', _, l) -> (
      (* Stub *)
      let sigma_app_l = prune_sigma (l :: sigma) in
      match
        List.find_opt (fun (e', sigma') -> e = e' && sigma_app_l = sigma') vis
      with
      | Some _ -> (StubResult { e; sigma = sigma_app_l }, set)
      | None -> (
          (* Application *)
          match analyze_aux e' sigma set vis with
          | ChoiceResult { choices; _ }, set_1 ->
              let result_list, set_union =
                fold_choices
                  (fun fun_res (result_accum, set_accum) ->
                    match fun_res with
                    | FunResult { f = Function (_, e_i, _); _ } ->
                        let res_i, set_i =
                          analyze_aux e_i sigma_app_l
                            ((l :: sigma) :: set_accum)
                            ((e, sigma_app_l) :: vis)
                        in
                        (res_i :: result_accum, set_i)
                    | _ -> failwith "funresult (appl)" [@coverage off])
                  ([], set_1) choices
              in
              ( ChoiceResult { choices = result_list; l; sigma = sigma_app_l },
                set_union )
          | _ -> failwith "choice (appl)" [@coverage off]))
  | Var (Ident x, l) -> (
      let sigma_hd = List.hd sigma in
      let sigma_tl = List.tl sigma in
      match get_outer_scope l with
      | Function (Ident x1, _, _) -> (
          if x = x1 then
            (* Var Local *)
            match get_expr sigma_hd with
            | Appl (_, e2, l') ->
                (* enumerate all matching stacks in the set *)
                let result_list, set_union =
                  List.fold_left
                    (fun ((result_accum, set_accum) as accum) sigma_i ->
                      if
                        List.hd sigma_i = l'
                        && contains_sigma (List.tl sigma_i) sigma_tl
                      then
                        let res_i, set_i =
                          analyze_aux e2 (List.tl sigma_i) set_accum vis
                        in
                        (res_i :: result_accum, set_i)
                      else accum)
                    ([], set) set
                in
                (ChoiceResult { choices = result_list; l; sigma }, set_union)
            | _ -> failwith "appl (var local)" [@coverage off]
          else
            (* Var Non-Local *)
            match get_expr sigma_hd with
            | Appl (e1, _, l2) -> (
                match analyze_aux e1 sigma set vis with
                | ChoiceResult { choices; _ }, set_1 ->
                    let result_list, set_union =
                      fold_choices
                        (fun fun_res (result_accum, set_accum) ->
                          match fun_res with
                          | FunResult
                              {
                                f = Function (Ident x1, _, _);
                                l = l1;
                                sigma = sigma_i;
                              } ->
                              let res_i, set_i =
                                analyze_aux
                                  (Var (Ident x, l1))
                                  sigma_i set_accum vis
                              in
                              (res_i :: result_accum, set_i)
                          | _ ->
                              (* TODO: throw or skip *)
                              failwith "FunResult (var non-local)"
                              [@coverage off])
                        ([], set_1) choices
                    in
                    (ChoiceResult { choices = result_list; l; sigma }, set_union)
                | _ -> failwith "choice" [@coverage off])
            | _ -> failwith "appl" [@coverage off])
      | _ -> failwith "function" [@coverage off])
  | Plus (e1, e2, _) ->
      (* hereafter we use short forms `r1` (`res1`), `s2` (`set2`), etc.
         as code is clearer here and thus they are less ambiguous. *)
      let vis' = (e, sigma) :: vis in
      let r1, s1 = analyze_aux e1 sigma set vis' in
      let r2, s2 = analyze_aux e2 sigma s1 vis' in
      (OpResult (PlusOp (r1, r2)), s2)
  | Minus (e1, e2, _) ->
      let vis' = (e, sigma) :: vis in
      let r1, s1 = analyze_aux e1 sigma set vis' in
      let r2, s2 = analyze_aux e2 sigma s1 vis' in
      (OpResult (MinusOp (r1, r2)), s2)
  | Equal (e1, e2, _) ->
      let vis' = (e, sigma) :: vis in
      let r1, s1 = analyze_aux e1 sigma set vis' in
      let r2, s2 = analyze_aux e2 sigma s1 vis' in
      (OpResult (EqualOp (r1, r2)), s2)
  | And (e1, e2, _) ->
      let vis' = (e, sigma) :: vis in
      let r1, s1 = analyze_aux e1 sigma set vis' in
      let r2, s2 = analyze_aux e2 sigma s1 vis' in
      (OpResult (AndOp (r1, r2)), s2)
  | Or (e1, e2, _) ->
      let vis' = (e, sigma) :: vis in
      let r1, s1 = analyze_aux e1 sigma set vis' in
      let r2, s2 = analyze_aux e2 sigma s1 vis' in
      (OpResult (OrOp (r1, r2)), s2)
  | Not (e', _) ->
      let r, s = analyze_aux e' sigma set ((e, sigma) :: vis) in
      (OpResult (NotOp r), s)
  | If (e', e1, e2, l) ->
      let vis' = (e, sigma) :: vis in
      let _r, s0 = analyze_aux e' sigma set vis' in
      (* TODO: eval r *)
      (* on stub, denote as `anynum` *)
      let r_true, s_true = analyze_aux e1 sigma set vis' in
      let r_false, s_false = analyze_aux e2 sigma set vis' in
      ( ChoiceResult { choices = [ r_true; r_false ]; l; sigma },
        s0 @ s_true @ s_false )
  | Let _ -> raise Unreachable [@coverage off]

let analyze e =
  let e = transform_let e in
  fill_my_fun e None;
  analyze_aux e [] [] []

(* TODO: multiple layers of ChoiceResult - improve output readability *)
