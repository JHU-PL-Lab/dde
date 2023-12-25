open Core
open Logs
open Interp.Ast

let ff = Format.fprintf
let prune_sigma ?(k = 2) s = List.filteri s ~f:(fun i _ -> i < k)

let rec starts_with sigma_parent sigma_child =
  match (sigma_parent, sigma_child) with
  | _, [] -> true
  | [], _ -> false
  | l_parent :: ls_parent, l_child :: ls_child ->
      l_parent = l_child && starts_with ls_parent ls_child

module S_key = struct
  module T = struct
    type t = sigma [@@deriving compare, sexp, show { with_path = false }, hash]
  end

  include T
  include Comparable.Make (T)
end

module St = struct
  module T = struct
    type lstate = int * sigma
    [@@deriving compare, sexp, hash, show { with_path = false }]

    type estate = expr * sigma
    [@@deriving compare, sexp, hash, show { with_path = false }]

    type t = Lstate of lstate | Estate of estate
    [@@deriving compare, sexp, hash, show { with_path = false }]
  end

  include T
  include Comparable.Make (T)
end

module V_key = struct
  module T = struct
    type lstate = int * sigma * string [@@deriving compare, sexp, hash]

    let show_lstate (l, sigma, s) =
      Format.sprintf "(%d, %s, %s)" l (S_key.show sigma) s

    let pp_lstate fmt lst = Format.fprintf fmt "%s" (show_lstate lst)

    type estate = expr * sigma * string [@@deriving compare, sexp, hash]

    let show_estate (e, sigma, s) =
      Format.asprintf "(%a, %s, %s)" Interp.Ast.pp_expr e (S_key.show sigma) s

    let pp_estate fmt est = Format.fprintf fmt "%s" (show_estate est)

    type t = Lstate of lstate | Estate of estate
    [@@deriving compare, sexp, hash]

    let show (k : t) =
      match k with
      | Lstate st -> Format.asprintf "%a" pp_lstate st
      | Estate st -> Format.asprintf "%a" pp_estate st
  end

  include T
  include Comparable.Make (T)
end

module Cache_key = struct
  module T = struct
    type t = expr * sigma * string * string [@@deriving compare, sexp, hash]
  end

  include T
  include Comparable.Make (T)
end

module V = struct
  module T = struct
    type t = Set.M(V_key).t [@@deriving compare, sexp]

    let show (v : t) =
      v |> Set.to_list |> List.map ~f:V_key.show |> String.concat ~sep:", "
      |> Format.sprintf "{%s}"
  end

  include T
  include Comparable.Make (T)
end

module S = struct
  module T = struct
    type t = Set.M(S_key).t [@@deriving compare, sexp]

    let show (s : t) =
      s |> Set.to_list |> List.map ~f:S_key.show |> String.concat ~sep:", "
      |> Format.sprintf "{%s}"
  end

  include T
  include Comparable.Make (T)
end

module Freq_key = struct
  module T = struct
    type t = expr * sigma * string * string [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

open Core
open Interp.Ast

module rec Atom : sig
  type t =
    | IntAnyAtom
    | IntAtom of int
    | BoolAtom of bool
    | FunAtom of expr * int * sigma
    | LStubAtom of (int * sigma)
    | EStubAtom of (expr * sigma)
    | RecAtom of (ident * Res.t) list
    | ProjAtom of Res.t * ident
    | InspAtom of ident * Res.t
    | AssertAtom of ident * Res.t * res_val_fv
  [@@deriving compare, sexp]

  val pp : Format.formatter -> Atom.t -> unit
end = struct
  type t =
    | IntAnyAtom
    | IntAtom of int
    | BoolAtom of bool
    | FunAtom of expr * int * sigma
    | LStubAtom of (int * sigma)
    | EStubAtom of (expr * sigma)
    | RecAtom of (ident * Res.t) list
    | ProjAtom of Res.t * ident
    | InspAtom of ident * Res.t
    | AssertAtom of ident * Res.t * res_val_fv
  [@@deriving compare, sexp]

  let rec pp_record fmt = function
    | [] -> ()
    | [ (Ident x, v) ] -> Format.fprintf fmt "%s = %a" x Res.pp v
    | (Ident x, r) :: rest ->
        Format.fprintf fmt "%s = %a; %a" x Res.pp r pp_record rest

  and pp fmt = function
    | IntAnyAtom -> ff fmt "Int"
    | IntAtom i -> ff fmt "%d" i
    | BoolAtom b -> ff fmt "%b" b
    | FunAtom (f, _, _) -> Interp.Pp.pp_expr fmt f
    | LStubAtom (l, sigma) ->
        (* ff fmt "stub@(%d,%a)" l pp_sigma sigma *)
        ff fmt "stub"
    | EStubAtom (e, sigma) ->
        (* ff fmt "stub@(%a,%a)" Interp.Pp.pp_expr e pp_sigma sigma *)
        ff fmt "stub"
    | RecAtom entries ->
        ff fmt
          (if List.length entries = 0 then "{%a}" else "{ %a }")
          pp_record entries
    | ProjAtom (r, Ident s) -> ff fmt "(%a.%s)" Res.pp r s
    | InspAtom (Ident s, r) -> ff fmt "(%s in %a)" s Res.pp r
    | AssertAtom (_, r, _) -> ff fmt "%a" Res.pp r
end

and Res_key : sig
  type t = Atom.t [@@deriving compare, sexp]
  type comparator_witness

  val comparator : (t, comparator_witness) Comparator.t
end = struct
  module T = struct
    type t = Atom.t [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

and Res : sig
  type t = Set.M(Res_key).t [@@deriving compare, sexp]

  val pp : Format.formatter -> Res.t -> unit
end = struct
  type t = Set.M(Res_key).t [@@deriving compare, sexp]

  let rec pp_aux fmt = function
    | [] -> ()
    | [ a ] -> ff fmt "%a" Atom.pp a
    | a :: _as -> ff fmt "%a | %a" Atom.pp a pp_aux _as

  and pp fmt r =
    if Set.is_empty r then ff fmt "#" else ff fmt "%a" pp_aux (Set.elements r)
end

type pi = (Res.t * bool) option [@@deriving compare]

let empty_res = Set.empty (module Res_key)
let single_res = Set.singleton (module Res_key)

(** Reader-State monad threaded through the analysis *)
module ReaderState = struct
  module T = struct
    type cache = Res.t Map.M(Cache_key).t
    type vids = string Map.M(V).t
    type sids = string Map.M(S).t
    type freqs = int64 Map.M(Freq_key).t
    type env = { v : V.t; vids : vids; cnt : int; rerun : bool; iter : int }
    type state = { s : S.t; c : cache; freqs : freqs; sids : sids; cnt : int }
    type 'a t = env -> state -> 'a * state

    let return (a : 'a) : 'a t = fun _ st -> (a, st)

    let bind (m : 'a t) ~(f : 'a -> 'b t) : 'b t =
     fun env st ->
      let a, st' = m env st in
      f a env st'

    let map = `Define_using_bind
    let ask () : env t = fun env st -> (env, st)

    let local (f : env -> env) (m : 'a t) : 'a t =
     fun env st ->
      let ({ v; vids; cnt; _ } as env') = f env in
      let vids', cnt' =
        if Map.mem vids v then (vids, cnt)
        else (Map.add_exn vids ~key:v ~data:(Format.sprintf "V%d" cnt), cnt + 1)
      in
      m { env' with vids = vids'; cnt = cnt' } st

    let get () : state t = fun _ st -> (st, st)
    let get_vid v : string t = fun { vids; _ } st -> (Map.find_exn vids v, st)

    let get_sid s : string t =
     fun _ ({ sids; _ } as st) -> (Map.find_exn sids s, st)

    let set_s s : unit t =
     fun _ ({ sids; cnt; _ } as st) ->
      let sids', cnt' =
        if Map.mem sids s then (sids, cnt)
        else (Map.add_exn sids ~key:s ~data:(Format.sprintf "S%d" cnt), cnt + 1)
      in
      ((), { st with s; sids = sids'; cnt = cnt' })

    let set_cache c : unit t = fun _ st -> ((), { st with c })

    let inc_freq freq_key : unit t =
     fun _ ({ freqs; _ } as st) ->
      let freqs' =
        match Map.find freqs freq_key with
        | None -> Map.add_exn freqs ~key:freq_key ~data:1L
        | Some freq ->
            Map.add_exn
              (Map.remove freqs freq_key)
              ~key:freq_key
              ~data:Int64.(freq + 1L)
      in
      ((), { st with freqs = freqs' })
  end

  include T
  include Monad.Make (T)
end

(** max recursion depth ever reached by execution *)
let max_d = ref 0

let log_freqs ?(sort = true) freqs =
  freqs |> Map.to_alist |> fun freqs ->
  (if not sort then freqs
   else
     List.sort freqs ~compare:(fun (_, freq1) (_, freq2) ->
         Int64.descending freq1 freq2))
  |> List.iter ~f:(fun ((e, sigma, vid, sid), freq) ->
         debug (fun m ->
             m "(%a, %a, %s, %s) -> %Ld\n" Interp.Pp.pp_expr e pp_sigma sigma
               vid sid freq))

let log_vids ?(size = false) ?(sort = false) vids =
  vids |> Map.to_alist |> fun vids ->
  (if not sort then vids
   else
     List.sort vids ~compare:(fun (_, id1) (_, id2) ->
         String.descending id1 id2))
  |> List.iter ~f:(fun (key, data) ->
         if size then debug (fun m -> m "%d -> %s\n" (Set.length key) data)
         else debug (fun m -> m "%s -> %s\n" (V.show key) data))

let log_sids ?(size = false) =
  Map.iteri ~f:(fun ~key ~data ->
      if size then debug (fun m -> m "%d -> %s\n" (Set.length key) data)
      else debug (fun m -> m "%s -> %s\n" (S.show key) data))

let bool_tf_res = Set.of_list (module Res_key) [ BoolAtom true; BoolAtom false ]

let all_combs_int r1 r2 op =
  Set.fold r1 ~init:empty_res ~f:(fun acc a1 ->
      Set.fold r2 ~init:acc ~f:(fun acc a2 ->
          match (a1, a2) with
          | Atom.IntAtom b1, Atom.IntAtom b2 -> Set.add acc (IntAtom (op b1 b2))
          | _ -> Set.add acc IntAnyAtom))

let all_combs_bool r1 r2 op =
  Set.fold r1 ~init:empty_res ~f:(fun acc a1 ->
      Set.fold r2 ~init:acc ~f:(fun acc a2 ->
          match (a1, a2) with
          | Atom.BoolAtom b1, Atom.BoolAtom b2 ->
              Set.add acc (BoolAtom (op b1 b2))
          | _ -> Set.union acc bool_tf_res))

let all_combs_bool' r1 r2 op =
  Set.fold r1 ~init:empty_res ~f:(fun acc a1 ->
      Set.fold r2 ~init:acc ~f:(fun acc a2 ->
          match (a1, a2) with
          | Atom.IntAtom i1, Atom.IntAtom i2 ->
              Set.add acc (BoolAtom (op i1 i2))
          | _ -> Set.union acc bool_tf_res))
