open Core
open Interp.Ast
open Exns
open Utils
open Utils.Atom

let rec exists_stub r label =
  Set.exists r ~f:(function
    | FunAtom _ | IntAtom _ | IntAnyAtom | BoolAtom _ -> false
    | LStubAtom st -> St.(label = St.Lstate st)
    | EStubAtom st -> St.(label = St.Estate st)
    | RecAtom entries ->
        List.exists entries ~f:(fun (_, r) -> exists_stub r label)
    | ProjAtom (r, _) | InspAtom (_, r) | AssertAtom (_, r, _) ->
        exists_stub r label)

let elim_stub r label =
  if not (exists_stub r label) then r
  else
    let bases =
      Set.fold r ~init:empty_res ~f:(fun acc a ->
          match a with
          | RecAtom _ when not (exists_stub (single_res a) label) ->
              Set.add acc a
          | ProjAtom (r, Ident key) when not (exists_stub r label) -> (
              match Set.elements r with
              | [ RecAtom rs ] -> (
                  match
                    List.find rs ~f:(fun (Ident key', _) -> String.(key = key'))
                  with
                  | Some (_, r') when Set.length r' = 1 ->
                      Set.add acc (r' |> Set.elements |> List.hd_exn)
                  | _ -> raise Runtime_error)
              | _ -> acc)
          | FunAtom _ -> Set.add acc a
          | _ -> acc)
    in
    Set.fold r ~init:empty_res ~f:(fun acc a ->
        match a with
        | ProjAtom (r, Ident key) -> (
            match Set.elements r with
            | [ EStubAtom st ] when St.(label = Estate st) ->
                Set.fold bases ~init:acc ~f:(fun acc -> function
                  | RecAtom es -> (
                      match
                        List.find es ~f:(fun (Ident key', _) ->
                            String.(key = key'))
                      with
                      | Some (_, r) -> Set.union acc r
                      | None -> acc)
                  | _ -> raise Runtime_error)
            | _ -> Set.add acc a)
        (* (fun x -> x) | stub *)
        | EStubAtom st when St.(label = Estate st) -> acc
        | _ -> Set.add acc a)

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
