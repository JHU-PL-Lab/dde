open Core
open Interpreter.Ast
open Grammar

let prune_sigma ?(k = 2) s = List.filteri s ~f:(fun i _ -> i < k)

let rec starts_with sigma_parent sigma_child =
  match (sigma_parent, sigma_child) with
  | _, [] -> true
  | [], _ -> false
  | l_parent :: ls_parent, l_child :: ls_child ->
      l_parent = l_child && starts_with ls_parent ls_child

let rec fold_res r ~init ~f =
  match r with
  | LabelResAtom (r, _) :: rs | ExprResAtom (r, _) :: rs ->
      fold_res (r @ rs) ~init ~f
  | r :: rs -> fold_res rs ~init:(f init r) ~f
  | [] -> init

let s_set = Hashset.create 1000

let print_set () =
  Hashset.fold (fun s acc -> show_sigma s ^ "\n" ^ acc) s_set ""

let pp_pair fmt (l, s) = Format.fprintf fmt "(%d, %s)" l @@ show_sigma s
let pp_pair_list fmt ls = Format.pp_print_list pp_pair fmt ls
let is_debug_mode = ref false

let all_combs l1 l2 =
  Set.fold l1 ~init:[] ~f:(fun acc x ->
      Set.fold l2 ~init:[] ~f:(fun acc y -> (x, y) :: acc))

let ff = Format.fprintf

let rec pp_atom fmt = function
  | IntAtom x -> ff fmt "%d" x
  | BoolAtom b -> ff fmt "%b" b
  | FunAtom (f, _, _) -> Interpreter.Pp.pp_expr fmt f
  | LabelResAtom (choices, _) | ExprResAtom (choices, _) ->
      ff fmt "%a" pp_res choices
  (* ff fmt "(%a, %a, %a)" pp_res choices Interpreter.Pp.pp_expr e pp_sigma s *)
  | OpAtom op -> (
      match op with
      | PlusOp (r1, r2) -> ff fmt "(%a + %a)" pp_res r1 pp_res r2
      | MinusOp (r1, r2) -> ff fmt "(%a - %a)" pp_res r1 pp_res r2
      | EqualOp (r1, r2) -> ff fmt "(%a = %a)" pp_res r1 pp_res r2
      | AndOp (r1, r2) -> ff fmt "(%a and %a)" pp_res r1 pp_res r2
      | OrOp (r1, r2) -> ff fmt "(%a or %a)" pp_res r1 pp_res r2
      | GeOp (r1, r2) -> ff fmt "(%a >= %a)" pp_res r1 pp_res r2
      | GtOp (r1, r2) -> ff fmt "(%a > %a)" pp_res r1 pp_res r2
      | LeOp (r1, r2) -> ff fmt "(%a <= %a)" pp_res r1 pp_res r2
      | LtOp (r1, r2) -> ff fmt "(%a < %a)" pp_res r1 pp_res r2
      | NotOp r1 -> ff fmt "(not %a)" pp_res r1)
  | LabelStubAtom _ | ExprStubAtom _ -> ff fmt "stub"
  | PathCondAtom ((r, b), r') -> ff fmt "(%a = %b ⊩ %a)" pp_res r b pp_res r'
  (* | PathCondAtom (_, a) -> ff fmt "%a" pp_res a *)
  | RecordAtom entries ->
      ff fmt
        (if List.length entries = 0 then "{%a}" else "{ %a }")
        pp_record_atom entries
  | ProjectionAtom (r, Ident s) -> ff fmt "%a.%s" pp_res r s
  | InspectionAtom (Ident s, r) -> ff fmt "%s in %a" s pp_res r
  | AssertAtom (e1, e2) ->
      ff fmt "assert %a in %a" pp_res e1
        (* TODO: pretty print *)
        Interpreter.Ast.pp_result_value_fv e2

and pp_record_atom fmt = function
  | [] -> ()
  | [ (Ident x, v) ] -> Format.fprintf fmt "%s = %a" x pp_res v
  | (Ident x, v) :: rest ->
      Format.fprintf fmt "%s = %a; %a" x pp_res v pp_record_atom rest

and pp_res fmt = function
  | [] -> ()
  | [ a ] -> ff fmt "%a" pp_atom a
  | a :: _as -> ff fmt "(%a | %a)" pp_atom a pp_res _as

let verify_result r =
  let solver = Solver.solver in
  Solver.chcs_of_res r;
  let chcs = Solver.list_of_chcs () in
  Z3.Solver.add solver chcs;

  match Z3.Solver.check solver [] with
  | SATISFIABLE ->
      (* Format.printf "sat" *)
      (* let model = solver |> Z3.Solver.get_model |> Core.Option.value_exn in
         model |> Z3.Model.to_string |> pf "Model:\n%s\n\n"; *)
      (* solver |> Z3.Solver.to_string |> Format.printf "Solver:\n%s"; *)
      Solver.reset ()
  | UNSATISFIABLE ->
      Solver.reset ();
      failwith "unsat"
  | UNKNOWN ->
      Solver.reset ();
      failwith "unknown"
