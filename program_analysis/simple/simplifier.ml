open Core
open Interp.Ast
open Pa.Exns
open Grammar
open Grammar.Atom

let rec exists_stub r label =
  Set.exists r ~f:(function
    | FunAtom _ | IntAtom _ | IntAnyAtom | BoolAtom _ -> false
    | LStubAtom st -> St.(label = St.Lstate st)
    | EStubAtom st -> St.(label = St.Estate st)
    | RecAtom entries ->
        List.exists entries ~f:(fun (_, r) -> exists_stub r label)
    | ProjAtom (r, _) | InspAtom (_, r) | AssertAtom (_, r, _) ->
        exists_stub r label)

let rec simplify ?(pa = None) r =
  let r' =
    Set.fold r ~init:empty_res ~f:(fun acc a ->
        match a with
        | IntAtom _ | IntAnyAtom | BoolAtom _ | LStubAtom _ | EStubAtom _
        | FunAtom _ ->
            Set.add acc a
        | AssertAtom (id, r, rv) ->
            Set.add acc (AssertAtom (id, simplify r ~pa:(Some a), rv))
        | RecAtom rs ->
            Set.add acc
              (RecAtom
                 (List.map rs ~f:(fun (id, r) -> (id, simplify r ~pa:(Some a)))))
        | ProjAtom (r, id) ->
            Set.fold r ~init:acc ~f:(fun acc a ->
                match a with
                | RecAtom rs -> (
                    match
                      List.find rs ~f:(fun (id', _) -> compare_ident id id' = 0)
                    with
                    | Some (_, r) -> Set.union acc r
                    | None -> acc)
                | a ->
                    Set.add acc
                      (ProjAtom (Set.singleton (module Res_key) a, id)))
        | InspAtom (id, r) ->
            Set.fold r ~init:acc ~f:(fun acc -> function
              | RecAtom rs ->
                  Set.add acc
                    (BoolAtom
                       (List.exists rs ~f:(fun (id', _) ->
                            compare_ident id id' = 0)))
              | a ->
                  Set.add acc (InspAtom (id, Set.singleton (module Res_key) a))))
  in
  if Res.compare r r' = 0 then r' else simplify r' ~pa
