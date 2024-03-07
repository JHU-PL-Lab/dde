(** Simplification of simple analysis results *)

open Core
open Interp.Ast
open Exns
open Utils
open Utils.Atom

(** Checks if any disjunct has a stub with `label` *)
let rec exists_stub_atom label = function
  | FunAtom _ | IntAtom _ | IntAnyAtom | BoolAtom _ -> false
  | LStubAtom st -> St.(label = St.Lstate st)
  | EStubAtom st -> St.(label = St.Estate st)
  | RecAtom entries ->
      List.exists entries ~f:(fun (_, r) -> exists_stub_res label r)
  | ProjAtom (r, _) | InspAtom (_, r) | AssertAtom (_, r, _) ->
      exists_stub_res label r

(** Checks if any disjunct in result has a stub with `label` *)
and exists_stub_res label = Set.exists ~f:(exists_stub_atom label)

(** Removes stubs without a parent - lone stubs that don't form a cycle *)
let elim_stub label r =
  if not (exists_stub_res label r) then r
  else
    let bases =
      Set.fold r ~init:empty_res ~f:(fun acc a ->
          match a with
          | RecAtom _ when not (exists_stub_atom label a) -> Set.add acc a
          | ProjAtom (r, Ident key) when not (exists_stub_res label r) -> (
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

(** Performs simplifications on value atoms *)
let rec simpl_atom a =
  match a with
  | IntAtom _ | IntAnyAtom | BoolAtom _ | LStubAtom _ | EStubAtom _ | FunAtom _
    ->
      single_res a
  | AssertAtom (id, r, rv) -> single_res (AssertAtom (id, simpl_res r, rv))
  | RecAtom rs ->
      single_res (RecAtom (List.map rs ~f:(fun (id, r) -> (id, simpl_res r))))
  | ProjAtom (r, id) ->
      Set.fold r ~init:empty_res ~f:(fun acc -> function
        | RecAtom rs -> (
            match List.find rs ~f:(fun (id', _) -> Ident.(id = id')) with
            | Some (_, r) -> Set.union acc r
            | None -> acc)
        | a -> Set.add acc (ProjAtom (single_res a, id)))
  | InspAtom (id, r) ->
      Set.fold r ~init:empty_res ~f:(fun acc -> function
        | RecAtom rs ->
            Set.add acc
              (BoolAtom (List.exists rs ~f:(fun (id', _) -> Ident.(id = id'))))
        | a -> Set.add acc (InspAtom (id, single_res a)))

(** Performs simplifications on value results *)
and simpl_res r =
  Set.fold r ~init:empty_res ~f:(fun acc a -> a |> simpl_atom |> Set.union acc)
  (* Stops when there's no change to the input result *)
  |> fun r' -> if Res.(r = r') then r' else simpl_res r'
