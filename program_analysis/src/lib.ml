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

let print_set () =
  Hashset.fold (fun sigma acc -> show_sigma_t sigma ^ "\n" ^ acc) s_set ""

module VSet = Set.Make (struct
  type t = expr * sigma_t * int

  let compare (l1, sigma1, _) (l2, sigma2, _) =
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

type maybe_int = DefInt of int | AnyInt
type maybe_bool = DefBool of bool | AnyBool

let rec eval_int res =
  match res with
  | BoolResult _ | FunResult _ -> raise Bad_type
  | IntResult i -> [ DefInt i ]
  | OpResult op_res -> (
      match op_res with
      | PlusOp (i1, i2) | MinusOp (i1, i2) ->
          let i1s = eval_int i1 in
          let i2s = eval_int i2 in
          all_combs i1s i2s
          |> List.map (function
               | DefInt x, DefInt y ->
                   DefInt
                     (match op_res with
                     | PlusOp _ -> x + y
                     | MinusOp _ -> x - y
                     | _ -> raise Unreachable [@coverage off])
               | _ -> AnyInt)
          |> List.sort_uniq compare
      | _ -> raise Unreachable [@coverage off])
  | ChoiceResult { choices; _ } ->
      List.map eval_int choices |> List.concat |> List.sort_uniq compare
  | StubResult _ -> [ AnyInt ]

and eval_bool res =
  match res with
  | IntResult _ | FunResult _ -> raise Bad_type
  | BoolResult b -> [ DefBool b ]
  | OpResult op_res -> (
      match op_res with
      | EqualOp (i1, i2) ->
          let i1s = eval_int i1 in
          let i2s = eval_int i2 in
          all_combs i1s i2s
          |> List.map (function
               | DefInt x, DefInt y -> DefBool (x = y)
               | _ -> AnyBool)
          |> List.sort_uniq compare
      | AndOp (b1, b2) | OrOp (b1, b2) ->
          let b1s = eval_bool b1 in
          let b2s = eval_bool b2 in
          all_combs b1s b2s
          |> List.map (function
               | DefBool x, DefBool y ->
                   DefBool
                     (match op_res with
                     | AndOp _ -> x && y
                     | OrOp _ -> x || y
                     | _ -> raise Unreachable [@coverage off])
               | _ -> AnyBool)
          |> List.sort_uniq compare
      | NotOp b -> []
      | _ -> raise Unreachable [@coverage off])
  | ChoiceResult { choices; _ } ->
      List.map eval_bool choices |> List.concat |> List.sort_uniq compare
  | StubResult _ -> [ AnyBool ]

let rec process_maybe_bools bs =
  Core.List.fold_until bs ~init:[]
    ~f:(fun acc b ->
      match b with
      | AnyBool -> Stop [ true; false ]
      | DefBool b -> Continue (b :: acc))
    ~finish:Fun.id

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
      let vis_state = (expr, l_app_sigma, 0) in
      (if !is_debug_mode then Format.printf "Appl: %d\n" l) [@coverage off];
      match VSet.find_opt vis_state v_set with
      (* Application Stub
         - only actually stub on second pass *)
      | Some (_, _, pass) when pass = 1 ->
          Some (StubResult { e = expr; sigma = l_app_sigma })
      | _ -> (
          (* Application *)
          match%map analyze_aux e sigma v_set with
          | ChoiceResult { choices; _ } ->
              let res_list =
                fold_choices
                  (fun fun_res acc ->
                    match fun_res with
                    | FunResult { f = Function (_, e_i, _); _ } -> (
                        (* TODO: S contains not just application labels? *)
                        Hashset.add s_set (l :: sigma);
                        (* increment pass counter when appropriate *)
                        let vis_state =
                          if VSet.mem vis_state v_set then
                            ( Core.Tuple3.get1 vis_state,
                              Core.Tuple3.get2 vis_state,
                              1 )
                          else vis_state
                        in
                        (* remove the previous state from set;
                           we have to manually do this because our custom compare
                           function for VSet doesn't take the pass number into
                           account so VSet.add won't overwrite the old state *)
                        let v_set = VSet.remove vis_state v_set in
                        match
                          analyze_aux e_i l_app_sigma (VSet.add vis_state v_set)
                        with
                        | Some res_i -> res_i :: acc
                        | None -> acc)
                    | _ -> raise Unreachable [@coverage off])
                  choices []
              in
              ChoiceResult { choices = res_list; l; sigma = l_app_sigma }
          | _ -> raise Unreachable [@coverage off]))
  | Var (Ident x, l) -> (
      match get_myfun l with
      | Function (Ident x1, _, l_myfun) ->
          if x = x1 then (
            (* Var Local *)
            (if !is_debug_mode then
               Format.printf "Var Local:\n%s, %d\nsigma: %s\nS:\n%s" x l
                 (show_sigma_t sigma) (print_set ()))
            [@coverage off];
            if List.length sigma = 0 then (
              (Format.printf "Unreachable: Var Local empty sigma_0\n";
               None)
              [@coverage off])
            else
              let vis_state = (expr, sigma, 0) in
              match VSet.find_opt vis_state v_set with
              (* Var Local Stub *)
              | Some _ -> Some (StubResult { e = expr; sigma })
              | _ -> (
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
                  | _ -> raise Unreachable [@coverage off]))
          else (
            (* Var Non-Local *)
            (if !is_debug_mode then
               Format.printf "Var Non-Local:\n%s, %d\nsigma: %s\nS:\n%s" x l
                 (show_sigma_t sigma) (print_set ()))
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
      let bs = res |> eval_bool |> process_maybe_bools in
      let res_list =
        bs
        |> List.map (function
             | true -> analyze_aux e_true sigma v_set
             | false -> analyze_aux e_false sigma v_set)
        |> List.filter_map Fun.id
      in
      ChoiceResult { choices = res_list; l; sigma }
  | Plus (e1, e2) | Minus (e1, e2) | Equal (e1, e2) | And (e1, e2) | Or (e1, e2)
    ->
      let%bind r1 = analyze_aux e1 sigma v_set in
      let%map r2 = analyze_aux e2 sigma v_set in
      OpResult
        (match expr with
        | Plus _ -> PlusOp (r1, r2)
        | Minus _ -> MinusOp (r1, r2)
        | Equal _ -> EqualOp (r1, r2)
        | And _ -> AndOp (r1, r2)
        | Or _ -> OrOp (r1, r2)
        | _ -> raise Unreachable [@coverage off])
  | Not e ->
      let%map r = analyze_aux e sigma v_set in
      OpResult (NotOp r)
  | Let _ -> raise Unreachable [@coverage off]

let analyze ~debug e =
  is_debug_mode := debug;

  let e = transform_let e in
  build_myfun e None;
  let r = analyze_aux e [] VSet.empty in

  (if !is_debug_mode then (
     Format.printf "\n%s\n\n" @@ show_expr e;
     Format.printf "****** Label Table ******\n";
     print_myexpr myexpr;
     Format.printf "****** Label Table ******\n\n";
     Hashset.iter (fun s -> Format.printf "%s\n" (show_sigma_t s)) s_set))
  [@coverage off];

  clean_up ();

  Option.get r
