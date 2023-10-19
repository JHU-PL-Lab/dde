open Core
open Dinterp.Ast
open Grammar
open Utils

exception Unreachable
exception Runtime_error

let rec simplify r =
  let r' =
    Set.fold r ~init:dres_empty ~f:(fun acc a ->
        match a with
        | DAtom.DIntAtom _ | DBoolAtom _ | DFunAtom _ | DStubAtom _
        | DIntAnyAtom ->
            Set.add acc a
        | DRecAtom rs ->
            Set.add acc
              (DRecAtom (List.map rs ~f:(fun (id, r) -> (id, simplify r))))
        | DProjAtom (r, id) ->
            Set.fold r ~init:acc ~f:(fun acc -> function
              | DRecAtom rs -> (
                  match
                    List.find rs ~f:(fun (id', _) -> compare_ident id id' = 0)
                  with
                  | Some (_, r) -> Set.union acc r
                  | None -> acc)
              | a -> Set.add acc (DProjAtom (simplify (dres_singleton a), id)))
        | DInspAtom (id, r) ->
            Set.fold r ~init:acc ~f:(fun acc -> function
              | DRecAtom rs ->
                  Set.add acc
                    (DBoolAtom
                       (List.exists rs ~f:(fun (id', _) ->
                            compare_ident id id' = 0)))
              | a -> Set.add acc (DInspAtom (id, simplify (dres_singleton a)))))
  in
  if Set.compare_direct r r' = 0 then r' else simplify r'
