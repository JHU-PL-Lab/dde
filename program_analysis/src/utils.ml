open Core
open Interpreter.Ast
open Grammar

let pf = Format.printf
let pfl = pf "%s\n"
let prune_sigma ?(k = 2) s = List.filteri s ~f:(fun i _ -> i < k)

let rec starts_with sigma_parent sigma_child =
  match (sigma_parent, sigma_child) with
  | _, [] -> true
  | [], _ -> false
  | l_parent :: ls_parent, l_child :: ls_child ->
      l_parent = l_child && starts_with ls_parent ls_child

let show_set = Set.fold ~init:"" ~f:(fun acc s -> show_sigma s ^ "\n" ^ acc)
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
  | LabelResAtom (choices, _) -> ff fmt "%a" pp_res choices
  (* | LabelResAtom (choices, (l, _)) -> ff fmt "(%a)^%d" pp_res choices l *)
  | ExprResAtom (choices, _) -> ff fmt "%a" pp_res choices
  (* | ExprResAtom (choices, (e, _)) ->
      ff fmt "(%a)^%a" pp_res choices Interpreter.Pp.pp_expr e *)
  (* ff fmt "(%a, %a, %a)" pp_res choices Interpreter.Pp.pp_expr e pp_sigma s *)
  | OpAtom op -> (
      match op with
      | PlusOp (r1, r2) -> ff fmt "(%a + %a)" pp_res r1 pp_res r2
      | MinusOp (r1, r2) -> ff fmt "(%a - %a)" pp_res r1 pp_res r2
      | MultOp (r1, r2) -> ff fmt "(%a * %a)" pp_res r1 pp_res r2
      | EqualOp (r1, r2) -> ff fmt "(%a = %a)" pp_res r1 pp_res r2
      | AndOp (r1, r2) -> ff fmt "(%a and %a)" pp_res r1 pp_res r2
      | OrOp (r1, r2) -> ff fmt "(%a or %a)" pp_res r1 pp_res r2
      | GeOp (r1, r2) -> ff fmt "(%a >= %a)" pp_res r1 pp_res r2
      | GtOp (r1, r2) -> ff fmt "(%a > %a)" pp_res r1 pp_res r2
      | LeOp (r1, r2) -> ff fmt "(%a <= %a)" pp_res r1 pp_res r2
      | LtOp (r1, r2) -> ff fmt "(%a < %a)" pp_res r1 pp_res r2
      | NotOp r1 -> ff fmt "(not %a)" pp_res r1)
  | LabelStubAtom _ -> ff fmt "stub"
  (* | LabelStubAtom (l, _) -> ff fmt "stub@%d" l *)
  | ExprStubAtom _ -> ff fmt "stub"
  (* | ExprStubAtom (e, _) -> ff fmt "(stub@%a)" Interpreter.Pp.pp_expr e *)
  (* | EquivStubAtom (s, l) ->
      ff fmt "{%s}[%d]"
        (s |> Set.to_list
        |> List.map ~f:(fun st -> Format.sprintf "%s" (St.show st))
        |> String.concat ~sep:", ")
        l *)
  | PathCondAtom (_, r) -> ff fmt "%a" pp_res r
  (* | PathCondAtom ((r, b), r') -> ff fmt "(%a = %b ⊩ %a)" pp_res r b pp_res r' *)
  | RecordAtom entries ->
      ff fmt
        (if List.length entries = 0 then "{%a}" else "{ %a }")
        pp_record_atom entries
  | ProjectionAtom (r, Ident s) -> ff fmt "(%a.%s)" pp_res r s
  | InspectionAtom (Ident s, r) -> ff fmt "(%s in %a)" s pp_res r
  | AssertAtom (_, r, _) -> ff fmt "%a" pp_res r

and pp_record_atom fmt = function
  | [] -> ()
  | [ (Ident x, v) ] -> Format.fprintf fmt "%s = %a" x pp_res v
  | (Ident x, v) :: rest ->
      Format.fprintf fmt "%s = %a; %a" x pp_res v pp_record_atom rest

and pp_res fmt = function
  | [] -> ()
  | [ a ] -> ff fmt "%a" pp_atom a
  | a :: _as -> ff fmt "(%a | %a)" pp_atom a pp_res _as

type lop =
  | LPlusOp of lres * lres
  | LMinusOp of lres * lres
  | LMultOp of lres * lres
  | LEqualOp of lres * lres
  | LAndOp of lres * lres
  | LOrOp of lres * lres
  | LGeOp of lres * lres
  | LGtOp of lres * lres
  | LLeOp of lres * lres
  | LLtOp of lres * lres
  | LNotOp of lres

and latom =
  | LIntAtom of int * int
  | LBoolAtom of bool * int
  | LFunAtom of expr * int * sigma
  | LOpAtom of lop * int
  | LLabelResAtom of lres * St.lstate * int
  | LExprResAtom of lres * St.estate * int
  | LLabelStubAtom of St.lstate * int
  | LExprStubAtom of St.estate * int
  | LPathCondAtom of lpath_cond * lres
  | LRecordAtom of (ident * lres) list
  | LProjectionAtom of lres * ident
  | LInspectionAtom of ident * lres
  | LAssertAtom of ident * lres * Interpreter.Ast.result_value_fv

and lres = latom list

and lpath_cond = lres * bool
[@@deriving hash, sexp, compare, show { with_path = false }]

module LAtomKey = struct
  module T = struct
    type t = latom [@@deriving hash, sexp, compare]
  end

  include T
  include Comparable.Make (T)
end

module LResKey = struct
  module T = struct
    type t = lres [@@deriving hash, sexp, compare]
  end

  include T
  include Comparable.Make (T)
end

let rec ppp_latom fmt = function
  | LIntAtom (x, _) -> ff fmt "%d" x
  | LBoolAtom (b, _) -> ff fmt "%b" b
  | LFunAtom (f, _, _) -> Interpreter.Pp.pp_expr fmt f
  | LLabelResAtom (choices, _, _) | LExprResAtom (choices, _, _) ->
      ff fmt "%a" ppp_lres choices
  (* ff fmt "(%a, %a, %a)" pp_res choices Interpreter.Pp.pp_expr e pp_sigma s *)
  | LOpAtom (op, _) -> (
      match op with
      | LPlusOp (r1, r2) -> ff fmt "(%a + %a)" ppp_lres r1 ppp_lres r2
      | LMinusOp (r1, r2) -> ff fmt "(%a - %a)" ppp_lres r1 ppp_lres r2
      | LMultOp (r1, r2) -> ff fmt "(%a * %a)" ppp_lres r1 ppp_lres r2
      | LEqualOp (r1, r2) -> ff fmt "(%a = %a)" ppp_lres r1 ppp_lres r2
      | LAndOp (r1, r2) -> ff fmt "(%a and %a)" ppp_lres r1 ppp_lres r2
      | LOrOp (r1, r2) -> ff fmt "(%a or %a)" ppp_lres r1 ppp_lres r2
      | LGeOp (r1, r2) -> ff fmt "(%a >= %a)" ppp_lres r1 ppp_lres r2
      | LGtOp (r1, r2) -> ff fmt "(%a > %a)" ppp_lres r1 ppp_lres r2
      | LLeOp (r1, r2) -> ff fmt "(%a <= %a)" ppp_lres r1 ppp_lres r2
      | LLtOp (r1, r2) -> ff fmt "(%a < %a)" ppp_lres r1 ppp_lres r2
      | LNotOp r -> (
          match r with
          | [ LOpAtom (lop, l) ] -> (
              match lop with
              | LEqualOp (r1, r2) -> ff fmt "%a <> %a" ppp_lres r1 ppp_lres r2
              | LGeOp (r1, r2) ->
                  ff fmt "%a" ppp_latom (LOpAtom (LLtOp (r1, r2), l))
              | LGtOp (r1, r2) ->
                  ff fmt "%a" ppp_latom (LOpAtom (LLeOp (r1, r2), l))
              | LLeOp (r1, r2) ->
                  ff fmt "%a" ppp_latom (LOpAtom (LGtOp (r1, r2), l))
              | LLtOp (r1, r2) ->
                  ff fmt "%a" ppp_latom (LOpAtom (LGeOp (r1, r2), l))
              | _ -> failwith "unimplemented:160")
          | _ -> failwith "unimplemented:161"))
  | LLabelStubAtom _ | LExprStubAtom _ -> ff fmt "stub"
  (* | PathCondAtom ((r, b), r') -> ff fmt "(%a = %b ⊩ %a)" pp_res r b pp_res r' *)
  | LPathCondAtom (_, r) -> ff fmt "%a" ppp_lres r
  | LRecordAtom entries ->
      ff fmt
        (if List.length entries = 0 then "{%a}" else "{ %a }")
        pp_lrecord_atom entries
  | LProjectionAtom (r, Ident s) -> ff fmt "%a.%s" ppp_lres r s
  | LInspectionAtom (Ident s, r) -> ff fmt "%s in %a" s ppp_lres r
  | LAssertAtom (_, r, _) -> ff fmt "%a" ppp_lres r

and pp_lrecord_atom fmt = function
  | [] -> ()
  | [ (Ident x, v) ] -> Format.fprintf fmt "%s = %a" x ppp_lres v
  | (Ident x, v) :: rest ->
      Format.fprintf fmt "%s = %a; %a" x ppp_lres v pp_lrecord_atom rest

and ppp_lres fmt = function
  | [] -> ()
  | [ a ] -> ff fmt "%a" ppp_latom a
  | a :: _as -> ff fmt "(%a | %a)" ppp_latom a ppp_lres _as

let res_to_id = Hashtbl.create (module LResKey)
let atom_to_id = Hashtbl.create (module LAtomKey)
let nodes = Hashset.create 100
let edges = Hashtbl.create (module String)
let edge_props = Hashtbl.create (module String)
let siblings = Hashtbl.create (module String)
let fresh_id = ref (-1)

let get_next_id () =
  incr fresh_id;
  !fresh_id

let idr r =
  Format.sprintf "P%d" (Hashtbl.find_or_add res_to_id r ~default:get_next_id)

let ida a =
  Format.sprintf "P%d" (Hashtbl.find_or_add atom_to_id a ~default:get_next_id)

let add_node = Hashset.add nodes
let remove_node = Hashset.remove nodes

let add_edge hd tl =
  match Hashtbl.find edges hd with
  | None -> Hashtbl.add_exn edges ~key:hd ~data:(String.Set.singleton tl)
  | Some tls ->
      Hashtbl.remove edges hd;
      Hashtbl.add_exn edges ~key:hd ~data:(String.Set.add tls tl)

let remove_edge hd tl =
  match Hashtbl.find edges hd with
  | None -> ()
  | Some tls ->
      Hashtbl.remove edges hd;
      Hashtbl.add_exn edges ~key:hd ~data:(Set.remove tls tl)

let add_sibling p n =
  match Hashtbl.find siblings p with
  | None -> Hashtbl.add_exn siblings ~key:p ~data:(String.Set.singleton n)
  | Some ns ->
      Hashtbl.remove siblings p;
      Hashtbl.add_exn siblings ~key:p ~data:(String.Set.add ns n)

let remove_sibling p n =
  match Hashtbl.find siblings p with
  | None -> ()
  | Some ns ->
      Hashtbl.remove siblings p;
      Hashtbl.add_exn siblings ~key:p ~data:(Set.remove ns n)

let add_edge_prop e (k, v) =
  let p = Format.sprintf "%s=%s" k v in
  match Hashtbl.find edge_props e with
  | None -> Hashtbl.add_exn edge_props ~key:e ~data:(String.Set.singleton p)
  | Some ps ->
      Hashtbl.remove edge_props e;
      Hashtbl.add_exn edge_props ~key:e ~data:(String.Set.add ps p)

let op_symbol = function
  | LPlusOp _ -> "+"
  | LMinusOp _ -> "-"
  | LMultOp _ -> "*"
  | LEqualOp _ -> "="
  | LAndOp _ -> "&&"
  | LOrOp _ -> "||"
  | LNotOp _ -> "!"
  | LGeOp _ -> ">="
  | LGtOp _ -> ">"
  | LLeOp _ -> "<="
  | LLtOp _ -> "<"

let next_label = ref 100000

let get_next_label () =
  incr next_label;
  !next_label

let rec label_prim =
  List.map ~f:(function
    | IntAtom i -> LIntAtom (i, get_next_label ())
    | BoolAtom b -> LBoolAtom (b, get_next_label ())
    | FunAtom (e, l, s) -> LFunAtom (e, l, s)
    | OpAtom op ->
        LOpAtom
          ( (match op with
            | PlusOp (r1, r2) -> LPlusOp (label_prim r1, label_prim r2)
            | MinusOp (r1, r2) -> LMinusOp (label_prim r1, label_prim r2)
            | MultOp (r1, r2) -> LMultOp (label_prim r1, label_prim r2)
            | EqualOp (r1, r2) -> LEqualOp (label_prim r1, label_prim r2)
            | GeOp (r1, r2) -> LGeOp (label_prim r1, label_prim r2)
            | GtOp (r1, r2) -> LGtOp (label_prim r1, label_prim r2)
            | LeOp (r1, r2) -> LLeOp (label_prim r1, label_prim r2)
            | LtOp (r1, r2) -> LLtOp (label_prim r1, label_prim r2)
            | AndOp (r1, r2) -> LAndOp (label_prim r1, label_prim r2)
            | OrOp (r1, r2) -> LOrOp (label_prim r1, label_prim r2)
            | NotOp r -> LNotOp (label_prim r)),
            get_next_label () )
    | AssertAtom (id, r, assn) -> LAssertAtom (id, label_prim r, assn)
    | LabelResAtom (r, st) -> LLabelResAtom (label_prim r, st, get_next_label ())
    | ExprResAtom (r, st) -> LExprResAtom (label_prim r, st, get_next_label ())
    | PathCondAtom ((r_cond, b), r) ->
        LPathCondAtom ((label_prim r_cond, b), label_prim r)
    | LabelStubAtom st -> LLabelStubAtom (st, get_next_label ())
    | ExprStubAtom st -> LExprStubAtom (st, get_next_label ())
    | RecordAtom entries ->
        LRecordAtom (List.map entries ~f:(fun (id, r) -> (id, label_prim r)))
    | ProjectionAtom (r, id) -> LProjectionAtom (label_prim r, id)
    | _ as a ->
        Format.printf "%a" Grammar.pp_atom a;
        failwith "unimplemented:290")

let dot_of_result ?(display_path_cond = true) test_num r =
  let r = label_prim r in
  (* Logs.info (fun m -> m "AST: %a" pp_lres r); *)
  (* p is the parent *atom* of a *)
  (* l is the label of the enclosing labeled result, if any *)
  (* any cycle (particularly its start) should be unique in
     each path condition subtree *)
  let rec dot_of_atom a p cycles =
    let aid = ida a in
    match a with
    | LIntAtom (i, l) -> add_node (Format.sprintf "%s [label=\"%i\"];" aid i)
    | LBoolAtom (b, l) -> add_node (Format.sprintf "%s [label=\"%b\"];" aid b)
    | LOpAtom (op, _) -> (
        match op with
        | LPlusOp (r1, r2)
        | LMinusOp (r1, r2)
        | LEqualOp (r1, r2)
        | LMultOp (r1, r2)
        | LGeOp (r1, r2)
        | LGtOp (r1, r2)
        | LLeOp (r1, r2)
        | LLtOp (r1, r2)
        | LAndOp (r1, r2)
        | LOrOp (r1, r2) ->
            add_node (Format.sprintf "%s [label=\"%s\"];" aid (op_symbol op));
            add_edge aid (idr r1);
            add_edge aid (idr r2);
            dot_of_res r1 (Some a) cycles;
            dot_of_res r2 (Some a) cycles
        | LNotOp r ->
            add_node (Format.sprintf "%s [label=\"%s\"];" aid (op_symbol op));
            add_edge aid (idr r);
            dot_of_res r (Some a) cycles)
    | LLabelResAtom (r, st, l) ->
        (* always point to the lowest instance of such a disjunction *)
        add_node (Format.sprintf "%s [label=\"|\", shape=\"diamond\"];" aid);
        add_edge aid (idr r);
        let lst = St.Lstate st in
        dot_of_res r (Some a)
          (Map.add_exn (Map.remove cycles lst) ~key:lst ~data:aid)
    | LExprResAtom (r, st, l) ->
        add_node (Format.sprintf "%s [label=\"|\", shape=\"diamond\"];" aid);
        add_edge aid (idr r);
        let est = St.Estate st in
        dot_of_res r (Some a)
          (Map.add_exn (Map.remove cycles est) ~key:est ~data:aid)
    | LLabelStubAtom (st, _) -> (
        add_node (Format.sprintf "%s [label=\"stub\", shape=\"box\"];" aid);
        match Map.find cycles (St.Lstate st) with
        | Some dom_node ->
            let aid = Format.sprintf "%s:n" aid in
            let edge_id = Format.sprintf "%s_%s" dom_node aid in
            add_edge dom_node aid;
            add_edge_prop edge_id ("dir", "back")
        | None ->
            Format.printf "%s\n" (St.show_lstate st);
            failwith "Lone stub!")
    | LExprStubAtom (st, l) -> (
        add_node (Format.sprintf "%s [label=\"stub\", shape=\"box\"];" aid);
        match Map.find cycles (St.Estate st) with
        | Some dom_node ->
            let aid = Format.sprintf "%s:sw" aid in
            let edge_id = Format.sprintf "%s_%s" dom_node aid in
            add_edge dom_node aid;
            add_edge_prop edge_id ("dir", "back")
        | None ->
            Format.printf "%s\n" (St.show_estate st);
            failwith "Lone stub!")
    | LAssertAtom (_, r, _) ->
        add_node (Format.sprintf "%s [label=\"Assert\"];" aid);
        let rid = idr r in
        add_edge aid rid;
        dot_of_res r (Some a) cycles
    | LPathCondAtom ((r, b), r0) ->
        add_node (Format.sprintf "%s [label=\"⊩\"];" aid);
        (if b then (
           add_edge aid (idr r);
           dot_of_res r (Some a) cycles)
         else
           match r with
           | [ LOpAtom (lop, _) ] -> (
               match lop with
               | LEqualOp (r1, r2) ->
                   let a' = LOpAtom (LNotOp r, get_next_label ()) in
                   add_edge aid (ida a');
                   dot_of_atom a' (Some a) cycles
               | LGeOp (r1, r2) ->
                   let a' = LOpAtom (LLtOp (r1, r2), get_next_label ()) in
                   add_edge aid (ida a');
                   dot_of_atom a' (Some a) cycles
               | LGtOp (r1, r2) ->
                   let a' = LOpAtom (LLeOp (r1, r2), get_next_label ()) in
                   add_edge aid (ida a');
                   dot_of_atom a' (Some a) cycles
               | LLeOp (r1, r2) ->
                   let a' = LOpAtom (LGtOp (r1, r2), get_next_label ()) in
                   add_edge aid (ida a');
                   dot_of_atom a' (Some a) cycles
               | LLtOp (r1, r2) ->
                   let a' = LOpAtom (LGeOp (r1, r2), get_next_label ()) in
                   add_edge aid (ida a');
                   dot_of_atom a' (Some a) cycles
               | _ -> failwith "unimplemented:395")
           | _ -> raise Unreachable);
        add_edge aid (idr r0);
        dot_of_res r0 (Some a) cycles;
        ( (* match p with
             | None ->
                 (* incr fresh_id;
                    let parent_aid = Format.sprintf "P%d" !fresh_id in *)
                 failwith "TODO"
             | Some parent_a ->
                 let parent_aid = ida parent_a in
                 remove_edge parent_aid aid;
                 remove_sibling parent_aid aid;
                 let r0id = idr r0 in
                 add_edge parent_aid r0id;
                 ignore
                   (Hashtbl.add edge_labels
                      ~key:(Format.sprintf "%s_%s" parent_aid r0id)
                      ~data:
                        (match r with
                        | [ LOpAtom (op, _) ] ->
                            if b then Format.asprintf "%a" pp_lres r
                            else
                              Format.asprintf "%a" ppp_latom
                                (LOpAtom (LNotOp r, get_next_label ()))
                        | _ -> raise Unreachable));
                 dot_of_res r0 (Some parent_a) *) )
    | LRecordAtom entries ->
        add_node
          (Format.sprintf "%s [shape=record, label=\"%s\"]" aid
             (String.concat ~sep:"|"
                (List.map entries ~f:(fun (Ident id, r) ->
                     let entry_id = Format.sprintf "%s_%s" aid id in
                     add_edge (Format.sprintf "%s:%s" aid entry_id) (idr r);
                     dot_of_res r (Some a) cycles;
                     Format.sprintf "<%s> %s" entry_id id))))
    | _ ->
        Format.printf "%a\n" ppp_latom a;
        raise Unreachable
  and dot_of_res r p pl =
    let rid = idr r in
    match p with
    | None ->
        if List.length r = 1 then dot_of_atom (List.hd_exn r) None pl
        else
          List.iter r ~f:(fun a ->
              dot_of_atom a None pl;
              add_node (Format.sprintf "%s [label=\"|\"];" rid);
              add_edge rid (ida a))
    | Some p -> (
        let pid = ida p in
        add_sibling pid rid;
        match p with
        | LLabelResAtom _ | LExprResAtom _ ->
            remove_edge pid rid;
            remove_sibling pid rid;
            List.iter r ~f:(fun a ->
                let aid = ida a in
                add_edge pid aid;
                add_sibling pid aid;
                dot_of_atom a (Some p) pl)
        | _ ->
            if List.length r = 1 then (
              let a = List.hd_exn r in
              let aid = ida a in
              remove_edge pid rid;
              remove_sibling pid rid;
              add_edge pid aid;
              add_sibling pid aid;
              (* needs to be called last to remove edges to PathCondAtoms *)
              dot_of_atom a (Some p) pl)
            else
              List.iter r ~f:(fun a ->
                  dot_of_atom a (Some p) pl;
                  add_node (Format.sprintf "%s [label=\"|\"];" rid);
                  add_edge rid (ida a)))
  in
  dot_of_res r None (Map.empty (module St));
  let nodes_str = Hashset.fold (Format.sprintf "%s\n%s") nodes "" in
  let ranks_str =
    Hashtbl.fold siblings ~init:"" ~f:(fun ~key ~data acc ->
        (* https://stackoverflow.com/questions/44274518/how-can-i-control-within-level-node-order-in-graphvizs-dot/44274606#44274606 *)
        let rank2 = Format.sprintf "%s_rank2" key in
        if Set.length data = 1 then acc
        else
          Format.sprintf
            "%s\n\
             %s [style=invis];\n\
             {rank=same; rankdir=LR; %s -> %s [style=invis];}" acc rank2 rank2
            (String.concat ~sep:" -> " (Set.to_list data)))
  in
  let edges_str =
    Hashtbl.fold edges ~init:"" ~f:(fun ~key ~data acc ->
        String.Set.fold data ~init:acc ~f:(fun acc n ->
            let id = Format.sprintf "%s_%s" key n in
            let props =
              match Hashtbl.find edge_props id with
              | None -> ""
              | Some ps ->
                  Format.sprintf "[%s]"
                    (String.concat ~sep:"," (Set.to_list ps))
            in
            Format.sprintf "%s\n%s -> %s %s" acc key n props))
  in
  let dot_file = Format.sprintf "graph%d.dot" test_num in
  Out_channel.write_all dot_file
    ~data:
      (Format.sprintf
         "digraph G {\n\
          node [fontname=\"Monospace\"]\n\
          edge [fontname=\"Monospace\"]\n\
          %s%s\n\
          %s\n\
          }"
         nodes_str ranks_str edges_str);
  Hashtbl.clear res_to_id;
  Hashtbl.clear atom_to_id;
  Hashset.clear nodes;
  Hashtbl.clear edges;
  Hashtbl.clear edge_props;
  Hashtbl.clear siblings;
  fresh_id := -1
