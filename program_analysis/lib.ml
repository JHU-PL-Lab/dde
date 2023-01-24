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
  | StubResult of { e : expr; sigma : sigma_t }
  | IntResult of int
  | BoolResult of bool
[@@deriving show { with_path = false }]

let prune_sigma ?(k = 2) sigma = List.filteri (fun i _ -> i < k) sigma

let rec contains_sigma sigma_parent sigma_child =
  match (sigma_child, sigma_parent) with
  | [], [] -> true
  | [], _ -> true
  | _, [] -> false
  | l_child :: ls_child, l_parent :: ls_parent ->
      l_child = l_parent && contains_sigma ls_parent ls_child

let rec fold_choices f accum choices =
  match choices with
  | ChoiceResult { choices = choices'; _ } :: rest ->
      fold_choices f accum choices'
  | res :: rest -> fold_choices f (f res accum) rest
  | [] -> accum

let rec find_choice f choices =
  match choices with
  | ChoiceResult { choices = choices'; _ } :: rest -> find_choice f choices'
  | res :: rest -> if f res then res else find_choice f rest
  | [] -> failwith "choice not found" [@coverage off]

(* pass in result-set pair to be returned if not visited *)
let stub_base e sigma v res_pair =
  match List.find_opt (fun (sigma', e') -> sigma = sigma' && e = e') v with
  | Some _ -> (StubResult { e; sigma }, snd res_pair)
  | None -> res_pair

let rec stub_step e sigma set v =
  match List.find_opt (fun (sigma', e') -> sigma = sigma' && e = e') v with
  | Some _ -> (StubResult { e; sigma }, set)
  | None -> analyze_aux e sigma set v

(* TODO: can refactor to inline logic for Stub *)
and analyze_aux e sigma set vis =
  match e with
  | Int i -> stub_base e sigma vis (IntResult i, set)
  | Bool b -> stub_base e sigma vis (BoolResult b, set)
  | Function (_, _, l) ->
      (*? should ChoiceResult wrap all results? *)
      stub_base e sigma vis
        ( ChoiceResult { choices = [ FunResult { f = e; l; sigma } ]; l; sigma },
          set )
  | Appl (e', _, l) -> (
      let vis' = (sigma, e) :: vis in
      match stub_step e' sigma set vis' with
      | ChoiceResult { choices; _ }, _ ->
          let result_list, set_union =
            fold_choices
              (fun fun_res (result_accum, set_accum) ->
                match fun_res with
                | FunResult { f = Function (_, e_i, _); _ } ->
                    let sigma' = l :: sigma in
                    let res_i, set_i =
                      (*? set element insertion notation is a bit off *)
                      stub_step e_i (prune_sigma sigma') (sigma' :: set) vis'
                    in
                    (res_i :: result_accum, set_accum @ set_i)
                | _ -> failwith "funresult (appl)" [@coverage off])
              ([], []) choices
          in
          (ChoiceResult { choices = result_list; l; sigma }, set_union)
      | _ -> failwith "choice (appl)" [@coverage off])
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
                          stub_step e2 (List.tl sigma_i) set ((sigma, e) :: vis)
                        in
                        (* TODO: use hashset for S *)
                        (res_i :: result_accum, set_i @ set_accum)
                      else accum)
                    ([], []) set
                in
                ( ChoiceResult { choices = result_list; l; sigma = sigma_tl },
                  set_union )
            | _ -> failwith "appl (var local)" [@coverage off]
          else
            (* Var Non-Local *)
            match get_expr sigma_hd with
            | Appl (e1, _, l2) -> (
                let vis' = (sigma, e) :: vis in
                match stub_step e1 sigma set vis' with
                | ChoiceResult { choices; _ }, set1 -> (
                    (* TODO: disjunction; function with different sigmas *)
                    let fun_res =
                      find_choice
                        (fun res ->
                          match res with FunResult _ -> true | _ -> false)
                        choices
                    in
                    match fun_res with
                    | FunResult { f; l = l1; sigma = sigma1 } ->
                        stub_step (Var (Ident x, l1)) sigma1 set1 vis'
                    | _ -> failwith "fun" [@coverage off])
                | _ -> failwith "choice" [@coverage off])
            | _ -> failwith "appl" [@coverage off])
      | _ -> failwith "function" [@coverage off])
  | Plus (e1, e2, _) ->
      (* hereafter we use short forms `r1` (`res1`), `s2` (`set2`), etc.
         as code is clearer here and thus they are less ambiguous. *)
      let vis' = (sigma, e) :: vis in
      let r1, s1 = stub_step e1 sigma set vis' in
      let r2, s2 = stub_step e2 sigma s1 vis' in
      (OpResult (PlusOp (r1, r2)), s2)
  | Minus (e1, e2, _) ->
      let vis' = (sigma, e) :: vis in
      let r1, s1 = stub_step e1 sigma set vis' in
      let r2, s2 = stub_step e2 sigma s1 vis' in
      (OpResult (MinusOp (r1, r2)), s2)
  | Equal (e1, e2, _) ->
      let vis' = (sigma, e) :: vis in
      let r1, s1 = stub_step e1 sigma set vis' in
      let r2, s2 = stub_step e2 sigma s1 vis' in
      (OpResult (EqualOp (r1, r2)), s2)
  | And (e1, e2, _) ->
      let vis' = (sigma, e) :: vis in
      let r1, s1 = stub_step e1 sigma set vis' in
      let r2, s2 = stub_step e2 sigma s1 vis' in
      (OpResult (AndOp (r1, r2)), s2)
  | Or (e1, e2, _) ->
      let vis' = (sigma, e) :: vis in
      let r1, s1 = stub_step e1 sigma set vis' in
      let r2, s2 = stub_step e2 sigma s1 vis' in
      (OpResult (OrOp (r1, r2)), s2)
  | Not (e', _) ->
      let r, s = stub_step e' sigma set ((sigma, e) :: vis) in
      (OpResult (NotOp r), s)
  | If (e', e1, e2, l) ->
      let vis' = (sigma, e) :: vis in
      let _r, s0 = stub_step e' sigma set vis' in
      (* TODO: eval r *)
      (* on stub, denote as `anynum` *)
      let r_true, s_true = stub_step e1 sigma set vis' in
      let r_false, s_false = stub_step e2 sigma set vis' in
      ( ChoiceResult { choices = [ r_true; r_false ]; l; sigma },
        s0 @ s_true @ s_false )
  | Let _ -> raise Unreachable [@coverage off]

let analyze e =
  let e = transform_let e in
  fill_my_fun e None;
  analyze_aux e [] [] []

(* TODO: multiple layers of ChoiceResult - improve output readability *)
