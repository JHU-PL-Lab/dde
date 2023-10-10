open Core
open Grammar
open Interpreter.Ast

exception Unreachable
exception Runtime_error

let rec simplify r =
  let r' =
    List.concat_map r ~f:(fun a ->
        match a with
        | IntAtom _ | BoolAtom _ | LabelStubAtom _ | ExprStubAtom _ | FunAtom _
        | IntAllAtom ->
            [ a ]
        | AssertAtom (id, r, rv) -> [ AssertAtom (id, simplify r, rv) ]
        | RecordAtom entries ->
            [
              RecordAtom (List.map entries ~f:(fun (id, r) -> (id, simplify r)));
            ]
        | ProjectionAtom (r, (Ident key as x)) ->
            List.concat_map r ~f:(function
              | RecordAtom es -> (
                  match
                    List.find es ~f:(fun (Ident key', _) -> String.(key = key'))
                  with
                  | Some (_, r) -> r
                  | None ->
                      []
                      (* Format.printf "%a\n" pp_atom a;
                         raise Runtime_error *))
              | a -> [ ProjectionAtom (simplify [ a ], x) ])
        | InspectionAtom ((Ident key as x), r) ->
            List.map r ~f:(function
              | RecordAtom es ->
                  BoolAtom
                    (List.exists es ~f:(fun (Ident key', _) ->
                         String.(key = key')))
              | a -> InspectionAtom (x, simplify [ a ])))
  in
  if compare_res r r' = 0 then r' else simplify r'
