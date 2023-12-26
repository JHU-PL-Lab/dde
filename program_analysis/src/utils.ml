open Core
open Interp.Ast
open Grammar

let prune_sigma ?(k = 2) s = List.filteri s ~f:(fun i _ -> i < k)

let rec starts_with sigma_parent sigma_child =
  match (sigma_parent, sigma_child) with
  | _, [] -> true
  | [], _ -> false
  | l_parent :: ls_parent, l_child :: ls_child ->
      l_parent = l_child && starts_with ls_parent ls_child

let show_set = Set.fold ~init:"" ~f:(fun acc s -> show_sigma s ^ "\n" ^ acc)

let all_combs l1 l2 =
  Set.fold l1 ~init:[] ~f:(fun acc x ->
      Set.fold l2 ~init:[] ~f:(fun acc y -> (x, y) :: acc))

let ff = Format.fprintf

let rec pp_atom fmt = function
  | IntAtom x -> ff fmt "%d" x
  | BoolAtom b -> ff fmt "%b" b
  | FunAtom (f, _, _) -> Interp.Pp.pp_expr fmt f
  | LResAtom (choices, _) -> ff fmt "%a" pp_res choices
  | EResAtom (choices, _) -> ff fmt "%a" pp_res choices
  | LStubAtom _ -> ff fmt "stub"
  | EStubAtom _ -> ff fmt "stub"
  (* | LabelResAtom (choices, (l, _)) -> ff fmt "(%a)^%d" pp_res choices l
     | ExprResAtom (choices, (e, _)) ->
         ff fmt "(%a)^%a" pp_res choices Interpreter.Pp.pp_expr e
     | LabelStubAtom (l, _) -> ff fmt "stub@%d" l
     | ExprStubAtom (e, _) -> ff fmt "(stub@%a)" Interpreter.Pp.pp_expr e *)
  | PlusAtom (r1, r2) -> ff fmt "(%a + %a)" pp_res r1 pp_res r2
  | MinusAtom (r1, r2) -> ff fmt "(%a - %a)" pp_res r1 pp_res r2
  | MultAtom (r1, r2) -> ff fmt "(%a * %a)" pp_res r1 pp_res r2
  | EqAtom (r1, r2) -> ff fmt "(%a = %a)" pp_res r1 pp_res r2
  | AndAtom (r1, r2) -> ff fmt "(%a and %a)" pp_res r1 pp_res r2
  | OrAtom (r1, r2) -> ff fmt "(%a or %a)" pp_res r1 pp_res r2
  | GeAtom (r1, r2) -> ff fmt "(%a >= %a)" pp_res r1 pp_res r2
  | GtAtom (r1, r2) -> ff fmt "(%a > %a)" pp_res r1 pp_res r2
  | LeAtom (r1, r2) -> ff fmt "(%a <= %a)" pp_res r1 pp_res r2
  | LtAtom (r1, r2) -> ff fmt "(%a < %a)" pp_res r1 pp_res r2
  | NotAtom r1 -> ff fmt "(not %a)" pp_res r1
  (* | EquivStubAtom (s, l) ->
      ff fmt "{%s}[%d]"
        (s |> Set.to_list
        |> List.map ~f:(fun st -> Format.sprintf "%s" (St.show st))
        |> String.concat ~sep:", ")
        l *)
  | PathCondAtom (_, r) -> ff fmt "%a" pp_res r
  (* | PathCondAtom ((r, b), r') -> ff fmt "(%a = %b ⊩ %a)" pp_res r b pp_res r' *)
  | RecAtom entries ->
      ff fmt
        (if List.is_empty entries then "{%a}" else "{ %a }")
        pp_record_atom entries
  | ProjAtom (r, Ident s) -> ff fmt "(%a.%s)" pp_res r s
  | InspAtom (Ident s, r) -> ff fmt "(%s in %a)" s pp_res r
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

type latom =
  | LIntAtom of int * int
  | LBoolAtom of bool * int
  | LFunAtom of expr * int * sigma
  | LLResAtom of lres * St.lstate * int
  | LEResAtom of lres * St.estate * int
  | LLStubAtom of St.lstate * int
  | LEStubAtom of St.estate * int
  | LPathCondAtom of lpath_cond * lres
  | LPlusAtom of lres * lres * int
  | LMinusAtom of lres * lres * int
  | LMultAtom of lres * lres * int
  | LEqAtom of lres * lres * int
  | LGeAtom of lres * lres * int
  | LGtAtom of lres * lres * int
  | LLeAtom of lres * lres * int
  | LLtAtom of lres * lres * int
  | LAndAtom of lres * lres * int
  | LOrAtom of lres * lres * int
  | LNotAtom of lres * int
  | LRecAtom of (ident * lres) list * int
  | LProjAtom of lres * ident
  | LInspAtom of ident * lres
  | LAssertAtom of ident * lres * Interp.Ast.res_val_fv

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
  | LFunAtom (f, _, _) -> Interp.Pp.pp_expr fmt f
  | LLResAtom (choices, _, _) | LEResAtom (choices, _, _) ->
      ff fmt "%a" ppp_lres choices
  (* ff fmt "(%a, %a, %a)" pp_res choices Interpreter.Pp.pp_expr e pp_sigma s *)
  | LPlusAtom (r1, r2, _) -> ff fmt "(%a + %a)" ppp_lres r1 ppp_lres r2
  | LMinusAtom (r1, r2, _) -> ff fmt "(%a - %a)" ppp_lres r1 ppp_lres r2
  | LMultAtom (r1, r2, _) -> ff fmt "(%a * %a)" ppp_lres r1 ppp_lres r2
  | LEqAtom (r1, r2, _) -> ff fmt "(%a = %a)" ppp_lres r1 ppp_lres r2
  | LAndAtom (r1, r2, _) -> ff fmt "(%a and %a)" ppp_lres r1 ppp_lres r2
  | LOrAtom (r1, r2, _) -> ff fmt "(%a or %a)" ppp_lres r1 ppp_lres r2
  | LGeAtom (r1, r2, _) -> ff fmt "(%a >= %a)" ppp_lres r1 ppp_lres r2
  | LGtAtom (r1, r2, _) -> ff fmt "(%a > %a)" ppp_lres r1 ppp_lres r2
  | LLeAtom (r1, r2, _) -> ff fmt "(%a <= %a)" ppp_lres r1 ppp_lres r2
  | LLtAtom (r1, r2, _) -> ff fmt "(%a < %a)" ppp_lres r1 ppp_lres r2
  | LNotAtom (r, _) -> (
      match r with
      | [ LEqAtom (r1, r2, _) ] -> ff fmt "%a <> %a" ppp_lres r1 ppp_lres r2
      | [ LGeAtom (r1, r2, l) ] -> ff fmt "%a" ppp_latom (LLtAtom (r1, r2, l))
      | [ LGtAtom (r1, r2, l) ] -> ff fmt "%a" ppp_latom (LLeAtom (r1, r2, l))
      | [ LLeAtom (r1, r2, l) ] -> ff fmt "%a" ppp_latom (LGtAtom (r1, r2, l))
      | [ LLtAtom (r1, r2, l) ] -> ff fmt "%a" ppp_latom (LGeAtom (r1, r2, l))
      | _ -> failwith "unimplemented")
  | LLStubAtom _ | LEStubAtom _ -> ff fmt "stub"
  (* | PathCondAtom ((r, b), r') -> ff fmt "(%a = %b ⊩ %a)" pp_res r b pp_res r' *)
  | LPathCondAtom (_, r) -> ff fmt "%a" ppp_lres r
  | LRecAtom (es, _) ->
      ff fmt
        (if List.length es = 0 then "{%a}" else "{ %a }")
        pp_lrecord_atom es
  | LProjAtom (r, Ident s) -> ff fmt "%a.%s" ppp_lres r s
  | LInspAtom (Ident s, r) -> ff fmt "%s in %a" s ppp_lres r
  | LAssertAtom (_, r, _) -> ff fmt "Assert (%a)" ppp_lres r

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
let pc_switch = ref ""

let add_edge_prop eid (k, v) =
  let p = Format.sprintf "%s=%s" k v in
  match Hashtbl.find edge_props eid with
  | None -> Hashtbl.add_exn edge_props ~key:eid ~data:(String.Set.singleton p)
  | Some ps ->
      Hashtbl.remove edge_props eid;
      Hashtbl.add_exn edge_props ~key:eid ~data:(Set.add ps p)

let edge_id = Format.sprintf "%s_%s"

let add_edge hd tl =
  if String.(!pc_switch <> "") then
    add_edge_prop (edge_id hd tl) ("cluster", !pc_switch);
  match Hashtbl.find edges hd with
  | None -> Hashtbl.add_exn edges ~key:hd ~data:(String.Set.singleton tl)
  | Some tls ->
      Hashtbl.remove edges hd;
      Hashtbl.add_exn edges ~key:hd ~data:(Set.add tls tl)

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
      Hashtbl.add_exn siblings ~key:p ~data:(Set.add ns n)

let remove_sibling p n =
  match Hashtbl.find siblings p with
  | None -> ()
  | Some ns ->
      Hashtbl.remove siblings p;
      Hashtbl.add_exn siblings ~key:p ~data:(Set.remove ns n)

let op_symbol = function
  | LPlusAtom _ -> "+"
  | LMinusAtom _ -> "-"
  | LMultAtom _ -> "*"
  | LEqAtom _ -> "="
  | LAndAtom _ -> "&&"
  | LOrAtom _ -> "||"
  | LNotAtom _ -> "!"
  | LGeAtom _ -> ">="
  | LGtAtom _ -> ">"
  | LLeAtom _ -> "<="
  | LLtAtom _ -> "<"
  | _ -> raise Unreachable

let next_label = ref 100000

let get_next_label () =
  incr next_label;
  !next_label

let rec label_prim =
  List.map ~f:(function
    | IntAtom i -> LIntAtom (i, get_next_label ())
    | BoolAtom b -> LBoolAtom (b, get_next_label ())
    | FunAtom (e, l, s) -> LFunAtom (e, l, s)
    | PlusAtom (r1, r2) ->
        LPlusAtom (label_prim r1, label_prim r2, get_next_label ())
    | MinusAtom (r1, r2) ->
        LMinusAtom (label_prim r1, label_prim r2, get_next_label ())
    | MultAtom (r1, r2) ->
        LMultAtom (label_prim r1, label_prim r2, get_next_label ())
    | EqAtom (r1, r2) ->
        LEqAtom (label_prim r1, label_prim r2, get_next_label ())
    | GeAtom (r1, r2) ->
        LGeAtom (label_prim r1, label_prim r2, get_next_label ())
    | GtAtom (r1, r2) ->
        LGtAtom (label_prim r1, label_prim r2, get_next_label ())
    | LeAtom (r1, r2) ->
        LLeAtom (label_prim r1, label_prim r2, get_next_label ())
    | LtAtom (r1, r2) ->
        LLtAtom (label_prim r1, label_prim r2, get_next_label ())
    | AndAtom (r1, r2) ->
        LAndAtom (label_prim r1, label_prim r2, get_next_label ())
    | OrAtom (r1, r2) ->
        LOrAtom (label_prim r1, label_prim r2, get_next_label ())
    | NotAtom r -> LNotAtom (label_prim r, get_next_label ())
    | AssertAtom (id, r, assn) -> LAssertAtom (id, label_prim r, assn)
    | LResAtom (r, st) -> LLResAtom (label_prim r, st, get_next_label ())
    | EResAtom (r, st) -> LEResAtom (label_prim r, st, get_next_label ())
    | PathCondAtom ((r_cond, b), r) ->
        LPathCondAtom ((label_prim r_cond, b), label_prim r)
    | LStubAtom st -> LLStubAtom (st, get_next_label ())
    | EStubAtom st -> LEStubAtom (st, get_next_label ())
    | RecAtom entries ->
        LRecAtom
          ( List.map entries ~f:(fun (id, r) -> (id, label_prim r)),
            get_next_label () )
    | ProjAtom (r, id) -> LProjAtom (label_prim r, id)
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
  (* TODO: add parent res *)
  let rec dot_of_atom a p pid pr cycles =
    let aid = ida a in
    match a with
    | LIntAtom (i, _) -> add_node (Format.sprintf "%s [label=\"%d\"];" aid i)
    | LBoolAtom (b, _) -> add_node (Format.sprintf "%s [label=\"%b\"];" aid b)
    | LPlusAtom (r1, r2, _)
    | LMinusAtom (r1, r2, _)
    | LEqAtom (r1, r2, _)
    | LMultAtom (r1, r2, _)
    | LGeAtom (r1, r2, _)
    | LGtAtom (r1, r2, _)
    | LLeAtom (r1, r2, _)
    | LLtAtom (r1, r2, _)
    | LAndAtom (r1, r2, _)
    | LOrAtom (r1, r2, _) ->
        add_node (Format.sprintf "%s [label=\"%s\"];" aid (op_symbol a));
        add_edge aid (idr r1);
        add_edge aid (idr r2);
        dot_of_res r1 (Some a) (Some aid) pr cycles;
        dot_of_res r2 (Some a) (Some aid) pr cycles
    | LNotAtom (r, _) ->
        add_node (Format.sprintf "%s [label=\"%s\"];" aid (op_symbol a));
        add_edge aid (idr r);
        dot_of_res r (Some a) (Some aid) pr cycles
    | LLResAtom (r, st, _) ->
        (* always point to the lowest instance of such a disjunction *)
        add_node (Format.sprintf "%s [label=\"|\", shape=\"diamond\"];" aid);
        add_edge aid (idr r);
        let lst = St.Lstate st in
        dot_of_res r (Some a) (Some aid) pr
          (Map.add_exn (Map.remove cycles lst) ~key:lst ~data:aid)
    | LEResAtom (r, st, _) ->
        add_node (Format.sprintf "%s [label=\"|\", shape=\"diamond\"];" aid);
        add_edge aid (idr r);
        let est = St.Estate st in
        dot_of_res r (Some a) (Some aid) pr
          (Map.add_exn (Map.remove cycles est) ~key:est ~data:aid)
    | LLStubAtom (st, _) -> (
        add_node (Format.sprintf "%s [label=\"stub\"];" aid);
        match Map.find cycles (St.Lstate st) with
        | Some dom_node ->
            let aid = Format.sprintf "%s" aid in
            let eid = edge_id dom_node aid in
            add_edge dom_node aid;
            add_edge_prop eid ("dir", "back")
        | None -> failwith "lone stub"
        (* Logs.debug (fun m -> m "Lone stub: %s" (St.show_lstate st)) *))
    | LEStubAtom (st, _) -> (
        add_node (Format.sprintf "%s [label=\"stub\"];" aid);
        match Map.find cycles (St.Estate st) with
        | Some dom_node ->
            let aid = Format.sprintf "%s" aid in
            let eid = edge_id dom_node aid in
            add_edge dom_node aid;
            add_edge_prop eid ("dir", "back")
        | None -> failwith "lone stub"
        (* Logs.debug (fun m -> m "Lone stub: %s" (St.show_estate st)) *)
        (* Format.printf "Lone stub: %s\n" (St.show_estate st) *)
        (* failwith "Lone stub!" *))
    | LAssertAtom (Ident x, r, rv) ->
        add_node (Format.sprintf "%s [label=\"assert\"];" aid);
        let xid = Format.sprintf "%s_x" aid in
        add_node (Format.asprintf "%s [label=\"%s\"];" xid x);
        add_edge aid xid;
        let rid = idr r in
        add_edge xid rid;
        let rvid = Format.sprintf "%s_assn" aid in
        add_node
          (Format.asprintf "%s [label=\"%a\"];" rvid Interp.Pp.pp_res_val_fv rv);
        add_edge aid rvid;
        (* add_sibling aid xid;
           add_sibling aid rvid; *)
        dot_of_res r (Some a) (Some aid) pr cycles
    | LPathCondAtom ((r, b), r0) -> (
        (* add_node (Format.sprintf "%s [label=\"⊩\"];" aid);
           let p = Some a in
           let pid = Some aid in
           (if b then (
              let rid = idr r in
              add_edge aid rid;
              pc_switch := aid;
              dot_of_res r p pid cycles)
            else
              match r with
              | [ LEqAtom (r1, r2, _) ] ->
                  let a' = LNotAtom (r, get_next_label ()) in
                  add_edge aid (ida a');
                  dot_of_atom a' p pid pr cycles
              | [ LGeAtom (r1, r2, _) ] ->
                  let a' = LLtAtom (r1, r2, get_next_label ()) in
                  add_edge aid (ida a');
                  dot_of_atom a' p pid pr cycles
              | [ LGtAtom (r1, r2, _) ] ->
                  let a' = LLeAtom (r1, r2, get_next_label ()) in
                  add_edge aid (ida a');
                  dot_of_atom a' p pid pr cycles
              | [ LLeAtom (r1, r2, _) ] ->
                  let a' = LGtAtom (r1, r2, get_next_label ()) in
                  add_edge aid (ida a');
                  dot_of_atom a' p pid pr cycles
              | [ LLtAtom (r1, r2, _) ] ->
                  let a' = LGeAtom (r1, r2, get_next_label ()) in
                  add_edge aid (ida a');
                  dot_of_atom a' p pid pr cycles
              | [ LBoolAtom (b, _) ] ->
                  let a' = LBoolAtom (not b, get_next_label ()) in
                  add_edge aid (ida a');
                  dot_of_atom a' p pid pr cycles
              | _ ->
                  Format.printf "%a\n" pp_lres r;
                  raise Unreachable);
           add_edge aid (idr r0);
           dot_of_res r0 p pid cycles *)
        (* if Option.is_some pr then ( *)
        (* Logs.debug (fun m -> m "Atom: %a\n" ppp_latom a);
           Logs.debug (fun m -> m "Atom: %a\n" pp_latom a);
           Logs.debug (fun m -> m "Parent: %a\n" ppp_lres pr);
           Logs.debug (fun m -> m "Parent: %a\n" pp_lres pr); *)
        (* Format.printf "Atom: %a\n" ppp_latom a;
           Format.printf "Parent: %a\n" ppp_lres pr;
           Format.printf "Parent: %a\n" pp_lres pr; *)
        match pr with
        | Some pr ->
            (* TODO *)
            (* let pr = idr pr in *)
            (* remove_edge pr aid; *)
            (* add_edge pr (ida (List.hd_exn r0)); *)
            dot_of_res r0 p pid (Some pr) cycles
        | None -> (
            match p with
            | Some p ->
                let pid' = ida p in
                add_edge pid' (idr r0);
                dot_of_res r0 (Some p) pid pr cycles
            | None -> failwith "wtf"))
    | LRecAtom (rs, _) ->
        if List.is_empty rs then
          add_node
            (Format.sprintf "%s [label=\"&#123;&#125;\", shape=\"record\"]" aid)
        else
          add_node
            (Format.sprintf "%s [label=\"%s\", shape=\"record\"]" aid
               (String.concat ~sep:"|"
                  (List.mapi rs ~f:(fun i (Ident x, r) ->
                       let pid = Format.sprintf "%s:%s" aid x in
                       add_edge pid (idr r);
                       dot_of_res r (Some a) (Some pid) pr cycles;
                       Format.sprintf
                         (if i = 0 then "<%s>&#123; %s"
                          else if i = List.length rs - 1 then "<%s> %s &#125;"
                          else "<%s> %s")
                         x x))))
    | _ -> raise Unreachable
  and dot_of_res r p pid pr pl =
    let rid = idr r in
    match p with
    | None ->
        if List.length r = 1 then dot_of_atom (List.hd_exn r) None None None pl
        else
          List.iter r ~f:(function a ->
              dot_of_atom a None None (Some r) pl;
              add_node
                (Format.sprintf "%s [label=\"|\", shape=\"diamond\"];" rid)
              (* add_edge rid (ida a) *))
    | Some p -> (
        let pid' = ida p in
        match p with
        | LLResAtom _ | LEResAtom _ ->
            remove_edge pid' rid;
            List.iter r ~f:(function
              | LPathCondAtom _ as a ->
                  (* Format.printf "%a\n" ppp_lres r; *)
                  dot_of_atom a (Some p) pid None pl
              | a ->
                  let aid = ida a in
                  add_edge pid' aid;
                  add_sibling pid' aid;
                  dot_of_atom a (Some p) pid None pl)
        | LRecAtom _ ->
            if List.length r = 1 then (
              let a = List.hd_exn r in
              match a with
              | LPathCondAtom _ ->
                  let pid = Option.value_exn pid in
                  remove_edge pid rid;
                  dot_of_atom a (Some p) (Some pid) None pl
              | _ ->
                  let aid = ida a in
                  let pid = Option.value_exn pid in
                  remove_edge pid rid;
                  add_edge pid aid;
                  dot_of_atom a (Some p) (Some pid) None pl)
            else
              List.iter r ~f:(function
                | LPathCondAtom _ as a ->
                    dot_of_atom a (Some p) pid (Some r) pl;
                    add_node
                      (Format.sprintf "%s [label=\"|\", shape=\"diamond\"];" rid)
                | a ->
                    dot_of_atom a (Some p) pid (Some r) pl;
                    add_node
                      (Format.sprintf "%s [label=\"|\", shape=\"diamond\"];" rid);
                    add_edge rid (ida a))
        | _ ->
            add_sibling pid' rid;
            if List.length r = 1 then (
              let a = List.hd_exn r in
              match a with
              (* | LPathCondAtom _ ->
                  remove_edge pid' rid;
                  remove_sibling pid' rid;
                  (* needs to be called last to remove edges to PathCondAtoms *)
                  dot_of_atom a (Some p) pid (Some r) pl *)
              | _ ->
                  let aid = ida a in
                  remove_edge pid' rid;
                  remove_sibling pid' rid;
                  (* TODO *)
                  if Option.is_some pr then
                    (* Format.printf "%s\n" pid';
                       Format.printf "%a\n" pp_latom a; *)
                    (* add_edge pid' aid; *)
                    add_edge (idr (Option.value_exn pr)) (ida a)
                  else (
                    add_edge pid' aid;
                    add_sibling pid' aid);
                  (* needs to be called last to remove edges to PathCondAtoms *)
                  dot_of_atom a (Some p) pid None pl)
            else
              List.iter r ~f:(function
                  (* | LPathCondAtom _ as a ->
                      remove_edge pid' rid;
                      remove_sibling pid' rid;
                      remove_node rid;
                      (* Format.printf "%s\n" (idr r); *)
                      dot_of_atom a (Some p) pid (Some r) pl *)
                  | a ->
                  dot_of_atom a (Some p) pid (Some r) pl;
                  add_node
                    (Format.sprintf "%s [label=\"|\", shape=\"diamond\"];" rid)
                  (* add_edge rid (ida a) *)))
  in
  dot_of_res r None None None (Map.empty (module St));
  (* Hashtbl.iteri atom_to_id ~f:(fun ~key ~data ->
         Format.printf "%a -> %d\n" ppp_latom key data);
     Hashtbl.iteri res_to_id ~f:(fun ~key ~data ->
         Format.printf "%a -> %d\n" ppp_lres key data); *)
  let nodes_str = Hashset.fold (Format.sprintf "%s\n%s") nodes "" in
  (* let ranks_str =
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
     in *)
  let ranks_str = "" in
  let edges_str =
    Hashtbl.fold edges ~init:"" ~f:(fun ~key ~data acc ->
        Set.fold data ~init:acc ~f:(fun acc n ->
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
