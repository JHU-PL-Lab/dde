open Core
open Interp.Ast
open Utils

(* graph visualization utilities *)

module rec Latom : sig
  type t =
    | LIntAtom of int * int
    | LBoolAtom of bool * int
    | LFunAtom of expr * int * sigma
    | LLResAtom of Lres.t * St.lstate * int
    | LEResAtom of Lres.t * St.estate * int
    | LLStubAtom of St.lstate * int
    | LEStubAtom of St.estate * int
    | LPathCondAtom of (Lres.t * bool) * Lres.t
    | LPlusAtom of Lres.t * Lres.t * int
    | LMinusAtom of Lres.t * Lres.t * int
    | LMultAtom of Lres.t * Lres.t * int
    | LEqAtom of Lres.t * Lres.t * int
    | LGeAtom of Lres.t * Lres.t * int
    | LGtAtom of Lres.t * Lres.t * int
    | LLeAtom of Lres.t * Lres.t * int
    | LLtAtom of Lres.t * Lres.t * int
    | LAndAtom of Lres.t * Lres.t * int
    | LOrAtom of Lres.t * Lres.t * int
    | LNotAtom of Lres.t * int
    | LRecAtom of (ident * Lres.t) list * int
    | LProjAtom of Lres.t * ident
    | LInspAtom of ident * Lres.t
    | LAssertAtom of ident * Lres.t * Interp.Ast.res_val_fv
  [@@deriving hash, sexp, compare, show { with_path = false }]

  val mk : Atom.t -> t
  val get_symbol : t -> string
end = struct
  type t =
    | LIntAtom of int * int
    | LBoolAtom of bool * int
    | LFunAtom of expr * int * sigma
    | LLResAtom of Lres.t * St.lstate * int
    | LEResAtom of Lres.t * St.estate * int
    | LLStubAtom of St.lstate * int
    | LEStubAtom of St.estate * int
    | LPathCondAtom of (Lres.t * bool) * Lres.t
    | LPlusAtom of Lres.t * Lres.t * int
    | LMinusAtom of Lres.t * Lres.t * int
    | LMultAtom of Lres.t * Lres.t * int
    | LEqAtom of Lres.t * Lres.t * int
    | LGeAtom of Lres.t * Lres.t * int
    | LGtAtom of Lres.t * Lres.t * int
    | LLeAtom of Lres.t * Lres.t * int
    | LLtAtom of Lres.t * Lres.t * int
    | LAndAtom of Lres.t * Lres.t * int
    | LOrAtom of Lres.t * Lres.t * int
    | LNotAtom of Lres.t * int
    | LRecAtom of (ident * Lres.t) list * int
    | LProjAtom of Lres.t * ident
    | LInspAtom of ident * Lres.t
    | LAssertAtom of ident * Lres.t * Interp.Ast.res_val_fv
  [@@deriving hash, sexp, compare, show { with_path = false }]

  let rec pp fmt = function
    | Latom.LIntAtom (x, _) -> ff fmt "%d" x
    | LBoolAtom (b, _) -> ff fmt "%b" b
    | LFunAtom (f, _, _) -> Interp.Pp.pp_expr fmt f
    | LLResAtom (choices, _, _) | LEResAtom (choices, _, _) ->
        ff fmt "%a" Lres.pp choices
    | LPlusAtom (r1, r2, _) -> ff fmt "(%a + %a)" Lres.pp r1 Lres.pp r2
    | LMinusAtom (r1, r2, _) -> ff fmt "(%a - %a)" Lres.pp r1 Lres.pp r2
    | LMultAtom (r1, r2, _) -> ff fmt "(%a * %a)" Lres.pp r1 Lres.pp r2
    | LEqAtom (r1, r2, _) -> ff fmt "(%a = %a)" Lres.pp r1 Lres.pp r2
    | LAndAtom (r1, r2, _) -> ff fmt "(%a and %a)" Lres.pp r1 Lres.pp r2
    | LOrAtom (r1, r2, _) -> ff fmt "(%a or %a)" Lres.pp r1 Lres.pp r2
    | LGeAtom (r1, r2, _) -> ff fmt "(%a >= %a)" Lres.pp r1 Lres.pp r2
    | LGtAtom (r1, r2, _) -> ff fmt "(%a > %a)" Lres.pp r1 Lres.pp r2
    | LLeAtom (r1, r2, _) -> ff fmt "(%a <= %a)" Lres.pp r1 Lres.pp r2
    | LLtAtom (r1, r2, _) -> ff fmt "(%a < %a)" Lres.pp r1 Lres.pp r2
    | LNotAtom (r, _) -> (
        match r with
        | [ LEqAtom (r1, r2, _) ] -> ff fmt "%a <> %a" Lres.pp r1 Lres.pp r2
        | [ LGeAtom (r1, r2, l) ] -> ff fmt "%a" pp (LLtAtom (r1, r2, l))
        | [ LGtAtom (r1, r2, l) ] -> ff fmt "%a" pp (LLeAtom (r1, r2, l))
        | [ LLeAtom (r1, r2, l) ] -> ff fmt "%a" pp (LGtAtom (r1, r2, l))
        | [ LLtAtom (r1, r2, l) ] -> ff fmt "%a" pp (LGeAtom (r1, r2, l))
        | _ -> failwith "unimplemented")
    | LLStubAtom _ | LEStubAtom _ -> ff fmt "stub"
    (* | PathCondAtom ((r, b), r') -> ff fmt "(%a = %b ⊩ %a)" pp_res r b pp_res r' *)
    | LPathCondAtom (_, r) -> ff fmt "%a" Lres.pp r
    | LRecAtom (es, _) ->
        ff fmt
          (if List.length es = 0 then "{%a}" else "{ %a }")
          pp_lrecord_atom es
    | LProjAtom (r, Ident s) -> ff fmt "%a.%s" Lres.pp r s
    | LInspAtom (Ident s, r) -> ff fmt "%s in %a" s Lres.pp r
    | LAssertAtom (_, r, _) -> ff fmt "Assert (%a)" Lres.pp r

  and pp_lrecord_atom fmt = function
    | [] -> ()
    | [ (Ident x, v) ] -> Format.fprintf fmt "%s = %a" x Lres.pp v
    | (Ident x, v) :: rest ->
        Format.fprintf fmt "%s = %a; %a" x Lres.pp v pp_lrecord_atom rest

  let next_label = ref 100000

  let get_next_label () =
    incr next_label;
    !next_label

  let rec mk = function
    | Atom.IntAtom i -> Latom.LIntAtom (i, get_next_label ())
    | BoolAtom b -> LBoolAtom (b, get_next_label ())
    | FunAtom (e, l, s) -> LFunAtom (e, l, s)
    | PlusAtom (r1, r2) -> LPlusAtom (Lres.mk r1, Lres.mk r2, get_next_label ())
    | MinusAtom (r1, r2) ->
        LMinusAtom (Lres.mk r1, Lres.mk r2, get_next_label ())
    | MultAtom (r1, r2) -> LMultAtom (Lres.mk r1, Lres.mk r2, get_next_label ())
    | EqAtom (r1, r2) -> LEqAtom (Lres.mk r1, Lres.mk r2, get_next_label ())
    | GeAtom (r1, r2) -> LGeAtom (Lres.mk r1, Lres.mk r2, get_next_label ())
    | GtAtom (r1, r2) -> LGtAtom (Lres.mk r1, Lres.mk r2, get_next_label ())
    | LeAtom (r1, r2) -> LLeAtom (Lres.mk r1, Lres.mk r2, get_next_label ())
    | LtAtom (r1, r2) -> LLtAtom (Lres.mk r1, Lres.mk r2, get_next_label ())
    | AndAtom (r1, r2) -> LAndAtom (Lres.mk r1, Lres.mk r2, get_next_label ())
    | OrAtom (r1, r2) -> LOrAtom (Lres.mk r1, Lres.mk r2, get_next_label ())
    | NotAtom r -> LNotAtom (Lres.mk r, get_next_label ())
    | AssertAtom (id, r, assn) -> LAssertAtom (id, Lres.mk r, assn)
    | LResAtom (r, st) -> LLResAtom (Lres.mk r, st, get_next_label ())
    | EResAtom (r, st) -> LEResAtom (Lres.mk r, st, get_next_label ())
    | PathCondAtom ((r_cond, b), r) ->
        LPathCondAtom ((Lres.mk r_cond, b), Lres.mk r)
    | LStubAtom st -> LLStubAtom (st, get_next_label ())
    | EStubAtom st -> LEStubAtom (st, get_next_label ())
    | RecAtom entries ->
        LRecAtom
          ( List.map entries ~f:(fun (id, r) -> (id, Lres.mk r)),
            get_next_label () )
    | ProjAtom (r, id) -> LProjAtom (Lres.mk r, id)
    | _ as a ->
        Format.printf "%a" Atom.pp a;
        failwith "unimplemented:290"

  let get_symbol = function
    | Latom.LPlusAtom _ -> "+"
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
end

and Lres : sig
  type t = Latom.t list
  [@@deriving hash, sexp, compare, show { with_path = false }]

  val mk : Res.t -> t
end = struct
  type t = Latom.t list
  [@@deriving hash, sexp, compare, show { with_path = false }]

  let rec pp fmt = function
    | [] -> ()
    | [ a ] -> ff fmt "%a" Latom.pp a
    | a :: _as -> ff fmt "(%a | %a)" Latom.pp a pp _as

  let mk = List.map ~f:Latom.mk
end

module Latom_key = struct
  module T = struct
    type t = Latom.t [@@deriving hash, sexp, compare]
  end

  include T
  include Comparable.Make (T)
end

module Lres_key = struct
  module T = struct
    type t = Lres.t [@@deriving hash, sexp, compare]
  end

  include T
  include Comparable.Make (T)
end

module State = struct
  module T = struct
    type state = {
      rids : string Map.M(Lres_key).t;
      aids : string Map.M(Latom_key).t;
      nodes : Set.M(String).t;
      edges : String.Set.t Map.M(String).t;
      edge_props : String.Set.t Map.M(String).t;
      siblings : String.Set.t Map.M(String).t;
      cnt : int;
    }

    type 'a t = state -> 'a * state

    let return (a : 'a) : 'a t = fun st -> (a, st)

    let bind (m : 'a t) ~(f : 'a -> 'b t) : 'b t =
     fun st ->
      let a, st' = m st in
      f a st'

    let map = `Define_using_bind
    let get () : state t = fun st -> (st, st)

    let get_rid r : string t =
     fun ({ rids; cnt; _ } as st) ->
      match Map.find rids r with
      | Some rid -> (rid, st)
      | None ->
          let cnt' = cnt + 1 in
          let rid' = Format.sprintf "P%d" cnt' in
          let rids' = Map.add_exn rids ~key:r ~data:rid' in
          (rid', { st with rids = rids'; cnt = cnt' })

    let get_aid a : string t =
     fun ({ aids; cnt; _ } as st) ->
      match Map.find aids a with
      | Some aid -> (aid, st)
      | None ->
          let cnt' = cnt + 1 in
          let aid' = Format.sprintf "P%d" cnt' in
          let aids' = Map.add_exn aids ~key:a ~data:aid' in
          (aid', { st with aids = aids'; cnt = cnt' })

    let add_node n : unit t =
     fun ({ nodes; _ } as st) -> ((), { st with nodes = Set.add nodes n })

    let add_edge_prop eid (k, v) : unit t =
     fun ({ edge_props; _ } as st) ->
      let p = Format.sprintf "%s=%s" k v in
      match Map.find edge_props eid with
      | None ->
          ( (),
            {
              st with
              edge_props =
                Map.add_exn edge_props ~key:eid ~data:(String.Set.singleton p);
            } )
      | Some ps ->
          ( (),
            {
              st with
              edge_props =
                Map.add_exn
                  (Map.remove edge_props eid)
                  ~key:eid ~data:(Set.add ps p);
            } )

    let edge_id = Format.sprintf "%s_%s"

    let add_edge hd tl : unit t =
      let open String in
      fun ({ edges; _ } as st) ->
        match Map.find edges hd with
        | None ->
            ( (),
              {
                st with
                edges = Map.add_exn edges ~key:hd ~data:(Set.singleton tl);
              } )
        | Some tls ->
            ( (),
              {
                st with
                edges =
                  Map.add_exn (Map.remove edges hd) ~key:hd
                    ~data:(Set.add tls tl);
              } )

    let remove_edge hd tl : unit t =
     fun ({ edges; _ } as st) ->
      match Map.find edges hd with
      | None -> ((), st)
      | Some tls ->
          ( (),
            {
              st with
              edges =
                Map.add_exn (Map.remove edges hd) ~key:hd
                  ~data:(Set.remove tls tl);
            } )

    let add_sibling p n : unit t =
     fun ({ siblings; _ } as st) ->
      match Map.find siblings p with
      | None ->
          ( (),
            {
              st with
              siblings =
                Map.add_exn siblings ~key:p ~data:(String.Set.singleton n);
            } )
      | Some ns ->
          ( (),
            {
              st with
              siblings =
                Map.add_exn (Map.remove siblings p) ~key:p ~data:(Set.add ns n);
            } )

    let remove_sibling p n : unit t =
     fun ({ siblings; _ } as st) ->
      match Map.find siblings p with
      | None -> ((), st)
      | Some ns ->
          ( (),
            {
              st with
              siblings =
                Map.add_exn (Map.remove siblings p) ~key:p
                  ~data:(Set.remove ns n);
            } )
  end

  include T
  include Monad.Make (T)
end

open State
open State.Let_syntax

let dot_of_result ?(display_path_cond = true) test_num r =
  let r = Lres.mk r in
  (* p is the parent *atom* of a *)
  (* l is the label of the enclosing labeled result, if any *)
  (* any cycle (particularly its start) should be unique in
     each path condition subtree *)
  let rec dot_of_atom a p pid pr cycles : 'a T.t =
    let%bind aid = get_aid a in
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
        let%bind () =
          add_node
            (Format.sprintf "%s [label=\"%s\"];" aid (Latom.get_symbol a))
        in
        let%bind rid1 = get_rid r1 in
        let%bind rid2 = get_rid r2 in
        let%bind () = add_edge aid rid1 in
        let%bind () = add_edge aid rid2 in
        let%bind () = dot_of_res r1 (Some a) (Some aid) pr cycles in
        dot_of_res r2 (Some a) (Some aid) pr cycles
    | LNotAtom (r, _) ->
        let%bind () =
          add_node
            (Format.sprintf "%s [label=\"%s\"];" aid (Latom.get_symbol a))
        in
        let%bind rid = get_rid r in
        let%bind () = add_edge aid rid in
        dot_of_res r (Some a) (Some aid) pr cycles
    | LLResAtom (r, st, _) ->
        (* always point to the lowest instance of such a disjunction *)
        let%bind () =
          add_node (Format.sprintf "%s [label=\"|\", shape=\"diamond\"];" aid)
        in
        let%bind rid = get_rid r in
        let%bind () = add_edge aid rid in
        let lst = St.Lstate st in
        dot_of_res r (Some a) (Some aid) pr
          (Map.add_exn (Map.remove cycles lst) ~key:lst ~data:aid)
    | LEResAtom (r, st, _) ->
        let%bind () =
          add_node (Format.sprintf "%s [label=\"|\", shape=\"diamond\"];" aid)
        in
        let%bind rid = get_rid r in
        let%bind () = add_edge aid rid in
        let est = St.Estate st in
        dot_of_res r (Some a) (Some aid) pr
          (Map.add_exn (Map.remove cycles est) ~key:est ~data:aid)
    | LLStubAtom (st, _) -> (
        let%bind () = add_node (Format.sprintf "%s [label=\"stub\"];" aid) in
        match Map.find cycles (St.Lstate st) with
        | Some dom_node ->
            let eid = edge_id dom_node aid in
            let%bind () = add_edge dom_node aid in
            add_edge_prop eid ("dir", "back")
        | None -> failwith "lone stub")
    | LEStubAtom (st, _) -> (
        let%bind () = add_node (Format.sprintf "%s [label=\"stub\"];" aid) in
        match Map.find cycles (St.Estate st) with
        | Some dom_node ->
            let aid = Format.sprintf "%s" aid in
            let eid = edge_id dom_node aid in
            let%bind () = add_edge dom_node aid in
            add_edge_prop eid ("dir", "back")
        | None -> failwith "lone stub")
    | LAssertAtom (Ident x, r, rv) ->
        let%bind () = add_node (Format.sprintf "%s [label=\"assert\"];" aid) in
        let xid = Format.sprintf "%s_x" aid in
        let%bind () = add_node (Format.asprintf "%s [label=\"%s\"];" xid x) in
        let%bind () = add_edge aid xid in
        let%bind rid = get_rid r in
        let%bind () = add_edge xid rid in
        let rvid = Format.sprintf "%s_assn" aid in
        let%bind () =
          add_node
            (Format.asprintf "%s [label=\"%a\"];" rvid Interp.Pp.pp_res_val_fv
               rv)
        in
        let%bind () = add_edge aid rvid in
        dot_of_res r (Some a) (Some aid) pr cycles
    | LPathCondAtom ((r, b), r0) -> (
        match pr with
        | Some pr -> dot_of_res r0 p pid (Some pr) cycles
        | None -> (
            match p with
            | Some p ->
                let%bind pid' = get_aid p in
                let%bind r0id = get_rid r0 in
                let%bind () = add_edge pid' r0id in
                dot_of_res r0 (Some p) pid pr cycles
            | None -> failwith "p = None"))
    | LRecAtom (rs, _) ->
        if List.is_empty rs then
          add_node
            (Format.sprintf "%s [label=\"&#123;&#125;\", shape=\"record\"]" aid)
        else
          let%bind cells =
            List.foldi rs ~init:(return []) ~f:(fun i acc (Ident x, r) ->
                let%bind acc = acc in
                let pid = Format.sprintf "%s:%s" aid x in
                let%bind rid = get_rid r in
                let%bind () = add_edge pid rid in
                let%bind () = dot_of_res r (Some a) (Some pid) pr cycles in
                return
                  (Format.sprintf
                     (if i = 0 then "<%s>&#123; %s"
                      else if i = List.length rs - 1 then "<%s> %s &#125;"
                      else "<%s> %s")
                     x x
                  :: acc))
          in
          cells |> List.rev |> String.concat ~sep:"|"
          |> Format.sprintf "%s [label=\"%s\", shape=\"record\"]" aid
          |> add_node
    | _ -> raise Unreachable
  and dot_of_res r p pid pr pl : 'a T.t =
    let%bind rid = get_rid r in
    match p with
    | None ->
        if List.length r = 1 then dot_of_atom (List.hd_exn r) None None None pl
        else
          List.fold r ~init:(return ()) ~f:(fun _ a ->
              let%bind () = dot_of_atom a None None (Some r) pl in
              add_node
                (Format.sprintf "%s [label=\"|\", shape=\"diamond\"];" rid))
    | Some p -> (
        let%bind pid' = get_aid p in
        match p with
        | LLResAtom _ | LEResAtom _ ->
            let%bind () = remove_edge pid' rid in
            List.fold r ~init:(return ()) ~f:(fun _ -> function
              | LPathCondAtom _ as a -> dot_of_atom a (Some p) pid None pl
              | a ->
                  let%bind aid = get_aid a in
                  let%bind () = add_edge pid' aid in
                  let%bind () = add_sibling pid' aid in
                  dot_of_atom a (Some p) pid None pl)
        | LRecAtom _ ->
            if List.length r = 1 then
              let a = List.hd_exn r in
              match a with
              | LPathCondAtom _ ->
                  let pid = Option.value_exn pid in
                  let%bind () = remove_edge pid rid in
                  dot_of_atom a (Some p) (Some pid) None pl
              | _ ->
                  let%bind aid = get_aid a in
                  let pid = Option.value_exn pid in
                  let%bind () = remove_edge pid rid in
                  let%bind () = add_edge pid aid in
                  dot_of_atom a (Some p) (Some pid) None pl
            else
              List.fold r ~init:(return ()) ~f:(fun _ -> function
                | LPathCondAtom _ as a ->
                    let%bind () = dot_of_atom a (Some p) pid (Some r) pl in
                    add_node
                      (Format.sprintf "%s [label=\"|\", shape=\"diamond\"];" rid)
                | a ->
                    let%bind () = dot_of_atom a (Some p) pid (Some r) pl in
                    let%bind () =
                      add_node
                        (Format.sprintf "%s [label=\"|\", shape=\"diamond\"];"
                           rid)
                    in
                    let%bind aid = get_aid a in
                    add_edge rid aid)
        | _ ->
            let%bind () = add_sibling pid' rid in
            if List.length r = 1 then
              let a = List.hd_exn r in
              let%bind aid = get_aid a in
              let%bind () = remove_edge pid' rid in
              let%bind () = remove_sibling pid' rid in
              let%bind () =
                if Option.is_some pr then
                  let%bind prid = get_rid (Option.value_exn pr) in
                  add_edge prid aid
                else
                  let%bind () = add_edge pid' aid in
                  add_sibling pid' aid
              in
              (* needs to be called last to remove edges to PathCondAtoms *)
              dot_of_atom a (Some p) pid None pl
            else
              List.fold r ~init:(return ()) ~f:(fun _ a ->
                  let%bind () = dot_of_atom a (Some p) pid (Some r) pl in
                  add_node
                    (Format.sprintf "%s [label=\"|\", shape=\"diamond\"];" rid))
        )
  in

  let (), { nodes; edges; edge_props; _ } =
    dot_of_res r None None None
      (Map.empty (module St))
      {
        rids = Map.empty (module Lres_key);
        aids = Map.empty (module Latom_key);
        nodes = String.Set.empty;
        edges = String.Map.empty;
        edge_props = String.Map.empty;
        siblings = String.Map.empty;
        cnt = 0;
      }
  in
  let nodes_str = nodes |> Set.elements |> String.concat ~sep:"\n" in
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
    Map.fold edges ~init:"" ~f:(fun ~key ~data acc ->
        Set.fold data ~init:acc ~f:(fun acc n ->
            let id = Format.sprintf "%s_%s" key n in
            let props =
              match Map.find edge_props id with
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
         nodes_str ranks_str edges_str)
