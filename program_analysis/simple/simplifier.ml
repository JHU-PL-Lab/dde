open Core
open Interp.Ast
open Pa.Exns
open Grammar

let rec exists_stub r label =
  List.exists r ~f:(function
    | FunAtom _ | IntAtom _ | IntAnyAtom | BoolAtom _ -> false
    | LStubAtom st -> St.(label = St.Lstate st)
    | EStubAtom st -> St.(label = St.Estate st)
    | RecAtom entries ->
        List.exists entries ~f:(fun (_, r) -> exists_stub r label)
    | ProjAtom (r, _) | InspAtom (_, r) | AssertAtom (_, r, _) ->
        exists_stub r label)

let rec simplify ?(pa = None) r =
  let r' =
    List.filter_map r ~f:(fun a ->
        match a with
        | IntAtom _ | IntAnyAtom | BoolAtom _ | LStubAtom _ | EStubAtom _
        | FunAtom _ ->
            Some [ a ]
        | AssertAtom (id, r, rv) ->
            Some [ AssertAtom (id, simplify r ~pa:(Some a), rv) ]
        | RecAtom rs ->
            Some
              [
                RecAtom
                  (List.map rs ~f:(fun (id, r) -> (id, simplify r ~pa:(Some a))));
              ]
        | ProjAtom (r, id) ->
            Some
              (List.concat_map r ~f:(fun a ->
                   match a with
                   | RecAtom rs -> (
                       match
                         List.find rs ~f:(fun (id', _) ->
                             compare_ident id id' = 0)
                       with
                       | Some (_, r) -> r
                       | None ->
                           (* [ ProjAtom ([ a ], id) ] *)
                           [])
                   | a ->
                       (* Format.printf "%a\n" pp_atom a; *)
                       [ ProjAtom ([ a ], id) ]))
        | InspAtom (id, r) ->
            Some
              (List.concat_map r ~f:(function
                | RecAtom rs ->
                    [
                      BoolAtom
                        (List.exists rs ~f:(fun (id', _) ->
                             compare_ident id id' = 0));
                    ]
                | a -> [ InspAtom (id, [ a ]) ])))
  in
  let r' = List.concat r' in
  if compare_res r r' = 0 then r' else simplify r' ~pa
