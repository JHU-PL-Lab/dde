open Core
open Dinterp
open Grammar

let ff = Format.fprintf

let rec pp_datom fmt = function
  | DAtom.DIntAnyAtom -> ff fmt "Int"
  | DIntAtom i -> ff fmt "%d" i
  | DBoolAtom b -> ff fmt "%b" b
  | DFunAtom (e, _) -> Dinterp.Pp.pp_expr fmt e
  (* | DPlusAtom (r1, r2) ->
         ff fmt "(%a + %a)" pp_dres (Set.elements r1) pp_dres (Set.elements r2)
     | DMinusAtom (r1, r2) ->
         ff fmt "(%a - %a)" pp_dres (Set.elements r1) pp_dres (Set.elements r2)
     | DMultAtom (r1, r2) ->
         ff fmt "(%a * %a)" pp_dres (Set.elements r1) pp_dres (Set.elements r2)
     | DEqAtom (r1, r2) ->
         ff fmt "(%a = %a)" pp_dres (Set.elements r1) pp_dres (Set.elements r2)
     | DGeAtom (r1, r2) ->
         ff fmt "(%a >= %a)" pp_dres (Set.elements r1) pp_dres (Set.elements r2)
     | DGtAtom (r1, r2) ->
         ff fmt "(%a > %a)" pp_dres (Set.elements r1) pp_dres (Set.elements r2)
     | DLeAtom (r1, r2) ->
         ff fmt "(%a <= %a)" pp_dres (Set.elements r1) pp_dres (Set.elements r2)
     | DLtAtom (r1, r2) ->
         ff fmt "(%a < %a)" pp_dres (Set.elements r1) pp_dres (Set.elements r2)
     | DAndAtom (r1, r2) ->
         ff fmt "(%a && %a)" pp_dres (Set.elements r1) pp_dres (Set.elements r2)
     | DOrAtom (r1, r2) ->
         ff fmt "(%a || %a)" pp_dres (Set.elements r1) pp_dres (Set.elements r2)
     | DNotAtom r -> ff fmt "not %a" pp_dres (Set.elements r) *)
  | DRecAtom rs ->
      if List.length rs = 0 then ff fmt "{}" else ff fmt "{ %a }" pp_drec rs
  | DProjAtom (r, Ident x) -> ff fmt "%a.%s" pp_dres r x
  | DInspAtom (Ident x, r) -> ff fmt "%s in %a" x pp_dres r
  | DStubAtom _ -> ff fmt "stub"

and pp_drec fmt = function
  | [] -> ()
  | [ (Ast.Ident x, r) ] -> ff fmt "%s = %a" x pp_dres r
  | (Ast.Ident x, r) :: rs -> ff fmt "%s = %a; %a" x pp_dres r pp_drec rs

and pp_dres fmt r =
  r
  |> Set.map (module String) ~f:(Format.asprintf "%a" pp_datom)
  (* TODO: seems unavoidable *)
  |> Set.elements
  |> String.concat ~sep:" | " |> ff fmt "%s"

let pp_s fmt s =
  s
  |> Set.map (module String) ~f:(Format.asprintf "%a" Pp.pp_d)
  |> Set.elements |> String.concat ~sep:"; "
  |> fun s -> if String.length s = 0 then ff fmt "[]" else ff fmt "[ %s ]" s

let pp_v fmt v =
  v
  |> Set.map
       (module String)
       ~f:(fun (l, d, s) ->
         match Hashtbl.find_exn Ast.myexpr l with
         | Ast.DApp _ -> Format.asprintf "(%d * %a * %a)" l Pp.pp_d d pp_s s
         | e -> Format.asprintf "(%a * %a * %a)" Pp.pp_expr e Pp.pp_d d pp_s s)
  |> Set.elements |> String.concat ~sep:"\n" |> ff fmt "%s"

let dres_singleton = Set.singleton (module DRes_key)
let dres_empty = Set.empty (module DRes_key)
let s_empty = Set.empty (module DS_key)
