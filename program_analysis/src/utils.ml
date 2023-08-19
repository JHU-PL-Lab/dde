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

let rec fold_res r ~init ~f =
  match r with
  | LabelResAtom (r, _) :: rs | ExprResAtom (r, _) :: rs ->
      fold_res (r @ rs) ~init ~f
  | r :: rs -> fold_res rs ~init:(f init r) ~f
  | [] -> init

let s_set = Hashset.create 1000
let show_set () = Hashset.fold (fun s acc -> show_sigma s ^ "\n" ^ acc) s_set ""
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
      | MultOp (r1, r2) -> ff fmt "(%a * %a)" pp_res r1 pp_res r2
      | EqualOp (r1, r2) -> ff fmt "(%a = %a)" pp_res r1 pp_res r2
      | AndOp (r1, r2) -> ff fmt "(%a and %a)" pp_res r1 pp_res r2
      | OrOp (r1, r2) -> ff fmt "(%a or %a)" pp_res r1 pp_res r2
      | GeOp (r1, r2) -> ff fmt "(%a >= %a)" pp_res r1 pp_res r2
      | GtOp (r1, r2) -> ff fmt "(%a > %a)" pp_res r1 pp_res r2
      | LeOp (r1, r2) -> ff fmt "(%a <= %a)" pp_res r1 pp_res r2
      | LtOp (r1, r2) -> ff fmt "(%a < %a)" pp_res r1 pp_res r2
      | NotOp r1 -> ff fmt "(not %a)" pp_res r1)
  | LabelStubAtom _ | ExprStubAtom _ -> ff fmt "stub"
  (* | PathCondAtom ((r, b), r') -> ff fmt "(%a = %b ⊩ %a)" pp_res r b pp_res r' *)
  | PathCondAtom (_, a) -> ff fmt "%a" pp_res a
  | RecordAtom entries ->
      ff fmt
        (if List.length entries = 0 then "{%a}" else "{ %a }")
        pp_record_atom entries
  | ProjectionAtom (r, Ident s) -> ff fmt "%a.%s" pp_res r s
  | InspectionAtom (Ident s, r) -> ff fmt "%s in %a" s pp_res r
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

let res_to_id = Hashtbl.create (module ResKey)
let atom_to_id = Hashtbl.create (module AtomKey)
let node_set = Hashset.create 100
let edge_map = Hashtbl.create (module String)
let parent_atom = Hashtbl.create (module String)
let st_to_node = Hashtbl.create (module State)
let edge_label = Hashtbl.create (module String)
let fresh_id = ref (-1)

let idr r =
  Format.sprintf "P%d"
    (Hashtbl.find_or_add res_to_id r ~default:(fun () ->
         incr fresh_id;
         !fresh_id))

let ida a =
  Format.sprintf "P%d"
    (Hashtbl.find_or_add atom_to_id a ~default:(fun () ->
         incr fresh_id;
         !fresh_id))

let add_node = Hashset.add node_set
let remove_node = Hashset.remove node_set

let add_edge hd tl =
  match Hashtbl.find edge_map hd with
  | None -> Hashtbl.add_exn edge_map ~key:hd ~data:(String.Set.singleton tl)
  | Some tls ->
      Hashtbl.remove edge_map hd;
      Hashtbl.add_exn edge_map ~key:hd ~data:(String.Set.add tls tl)

let remove_edge hd tl =
  match Hashtbl.find edge_map hd with
  | None -> ()
  | Some tls ->
      Hashtbl.remove edge_map hd;
      Hashtbl.add_exn edge_map ~key:hd ~data:(Set.remove tls tl)

let dot_of_result test_num r =
  let rec dot_of_atom a p =
    let aid = ida a in
    (match p with
    | None -> ()
    | Some p ->
        ignore
          (Hashtbl.add parent_atom ~key:aid
             ~data:(Hashtbl.find_exn parent_atom (idr p))));
    match a with
    | IntAtom i -> add_node (Format.sprintf "%s [label=\"%i\"];" aid i)
    | BoolAtom b -> add_node (Format.sprintf "%s [label=\"%b\"];" aid b)
    | OpAtom op -> (
        match op with
        | PlusOp (r1, r2)
        | MinusOp (r1, r2)
        | MultOp (r1, r2)
        | AndOp (r1, r2)
        | OrOp (r1, r2) ->
            let op_symbol =
              match op with
              | PlusOp _ -> "+"
              | MinusOp _ -> "-"
              | MultOp _ -> "*"
              | AndOp _ -> "&&"
              | OrOp _ -> "||"
              | _ -> raise Unreachable
            in
            add_node (Format.sprintf "%s [label=\"%s\"];" aid op_symbol);
            add_edge aid (idr r1);
            add_edge aid (idr r2);
            dot_of_res r1 (Some a);
            dot_of_res r2 (Some a)
        | _ -> failwith "unimplemented")
    | LabelResAtom (r, st) ->
        ignore (Hashtbl.add st_to_node ~key:(State.Lstate st, 0) ~data:aid);
        add_node (Format.sprintf "%s [label=\"|\"];" aid);
        add_edge aid (idr r);
        dot_of_res r (Some a)
    | ExprResAtom (r, st) ->
        ignore (Hashtbl.add st_to_node ~key:(State.Estate st, 0) ~data:aid);
        add_node (Format.sprintf "%s [label=\"|\"];" aid);
        add_edge aid (idr r);
        dot_of_res r (Some a)
    | LabelStubAtom st ->
        add_node (Format.sprintf "%s [label=\"stub\"];" aid);
        add_edge aid (Hashtbl.find_exn st_to_node (State.Lstate st, 0))
    | ExprStubAtom st ->
        add_node (Format.sprintf "%s [label=\"stub\"];" aid);
        add_edge aid (Hashtbl.find_exn st_to_node (State.Estate st, 0))
    | AssertAtom (_, r, _) ->
        add_node (Format.sprintf "%s [label=\"Assert\"];" aid);
        let rid = idr r in
        add_edge aid rid;
        dot_of_res r (Some a)
    | PathCondAtom ((r, b), r0) -> (
        match Hashtbl.find_exn parent_atom aid with
        | None ->
            (* incr fresh_id;
               let parent_aid = Format.sprintf "P%d" !fresh_id in *)
            failwith "nah"
        | Some parent_a ->
            let parent_aid = ida parent_a in
            remove_edge parent_aid aid;
            let r0id = idr r0 in
            add_edge parent_aid r0id;
            ignore
              (Hashtbl.add edge_label
                 ~key:(Format.sprintf "%s_%s" parent_aid r0id)
                 ~data:(Format.asprintf "%a = %b" pp_res r b));
            dot_of_res r0 (Some parent_a))
    | _ ->
        Format.printf "%a\n" Grammar.pp_atom a;
        raise Unreachable
  and dot_of_res r p =
    let rid = idr r in
    let new_p = Some r in
    match p with
    | None ->
        ignore (Hashtbl.add parent_atom ~key:rid ~data:None);
        if List.length r = 1 then dot_of_atom (List.hd_exn r) new_p
        else
          List.iter r ~f:(fun a ->
              dot_of_atom a new_p;
              add_node (Format.sprintf "%s [label=\"|\"];" rid);
              add_edge rid (ida a))
    | Some p -> (
        let pid = ida p in
        ignore (Hashtbl.add parent_atom ~key:rid ~data:(Some p));
        match p with
        | LabelResAtom _ | ExprResAtom _ ->
            remove_edge pid rid;
            let label =
              Hashtbl.find edge_label (Format.sprintf "%s_%s" pid rid)
            in
            List.iter r ~f:(fun a ->
                let aid = ida a in
                add_edge pid aid;
                (match label with
                | Some label ->
                    (* Format.printf "pid: %s | aid: %s | rid: %s\n" pid aid rid;
                       Format.printf "edges labels:\n";
                       Hashtbl.iteri edge_label ~f:(fun ~key ~data ->
                           Format.printf "%s: %s\n" key data); *)
                    ignore
                      (Hashtbl.add edge_label
                         ~key:(Format.sprintf "%s_%s" pid aid)
                         ~data:label)
                | None -> ());
                dot_of_atom a new_p)
        | _ ->
            if List.length r = 1 then (
              let a = List.hd_exn r in
              let aid = ida a in
              remove_edge pid rid;
              add_edge pid aid;
              (match
                 Hashtbl.find edge_label (Format.sprintf "%s_%s" pid rid)
               with
              | Some label ->
                  (* Format.printf "pid: %s | aid: %s | rid: %s\n" pid aid rid;
                     Format.printf "edges labels:\n";
                     Hashtbl.iteri edge_label ~f:(fun ~key ~data ->
                         Format.printf "%s: %s\n" key data); *)
                  ignore
                    (Hashtbl.add edge_label
                       ~key:(Format.sprintf "%s_%s" pid aid)
                       ~data:label)
              | None -> ());
              (* needs to be called last to remove edges to PathCondAtoms *)
              dot_of_atom a new_p)
            else
              List.iter r ~f:(fun a ->
                  dot_of_atom a new_p;
                  add_node (Format.sprintf "%s [label=\"|\"];" rid);
                  add_edge rid (ida a)))
  in
  dot_of_res r None;
  let nodes = Hashset.fold (Format.sprintf "%s\n%s") node_set "" in
  let edges =
    Hashtbl.fold edge_map ~init:"" ~f:(fun ~key ~data acc ->
        String.Set.fold data ~init:acc ~f:(fun acc n ->
            let edge_id = Format.sprintf "%s_%s" key n in
            let label =
              match Hashtbl.find edge_label edge_id with
              | None -> ""
              | Some l ->
                  (* Format.printf "yo\n"; *)
                  l
            in
            Format.sprintf "%s\n%s -> %s [label=\"%s\", fontsize=\"8\"]" acc key
              n label))
  in
  let dot_file = Format.sprintf "graph%d.dot" test_num in
  Out_channel.write_all dot_file
    ~data:
      (Format.sprintf
         "digraph G {\n\
          node [fontname=\"Arial\"]\n\
          edge [fontname=\"Arial\"]\n\
          %s%s\n\
          }"
         nodes edges);
  Hashtbl.clear res_to_id;
  Hashtbl.clear atom_to_id;
  Hashset.clear node_set;
  Hashtbl.clear edge_map;
  Hashtbl.clear parent_atom;
  Hashtbl.clear st_to_node;
  Hashtbl.clear edge_label;
  fresh_id := -1
