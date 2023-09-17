open Core
open Option.Let_syntax
open Grammar
open Interpreter.Ast

exception Unreachable

let rec has_stub r st =
  List.exists r ~f:(function
    | IntAtom _ | BoolAtom _ | FunAtom _ -> false
    | LabelStubAtom lst -> St.compare (St.Lstate lst) st = 0
    | ExprStubAtom est -> St.compare (St.Estate est) st = 0
    | OpAtom op -> (
        match op with
        | PlusOp (r1, r2)
        | MinusOp (r1, r2)
        | MultOp (r1, r2)
        | EqualOp (r1, r2)
        | GeOp (r1, r2)
        | GtOp (r1, r2)
        | LeOp (r1, r2)
        | LtOp (r1, r2)
        | AndOp (r1, r2)
        | OrOp (r1, r2) ->
            has_stub r1 st || has_stub r2 st
        | NotOp r -> has_stub r st)
    | LabelResAtom (r, st') ->
        St.compare (St.Lstate st') st <> 0 && has_stub r st
    | ExprResAtom (r, st') ->
        St.compare (St.Estate st') st <> 0 && has_stub r st
    | PathCondAtom (_, r) -> has_stub r st
    | RecordAtom entries -> List.exists entries ~f:(fun (_, r) -> has_stub r st)
    | ProjectionAtom (r, _) -> has_stub r st
    | InspectionAtom (_, r) -> has_stub r st
    | AssertAtom (_, r, _) ->
        has_stub r st (* | _ -> failwith "unimplemented" *))

let rec has_fun r =
  List.exists r ~f:(fun a ->
      match a with
      | IntAtom _ | BoolAtom _ | OpAtom _ | RecordAtom _ | ProjectionAtom _
      | InspectionAtom _ ->
          false
      | FunAtom _ -> true
      | LabelResAtom (r, st) -> has_fun r
      | ExprResAtom (r, st) -> has_fun r
      | PathCondAtom (pc, r) -> has_fun r
      | LabelStubAtom _ | ExprStubAtom _ -> false
      | _ -> failwith "unimplemented")

let rec simplify ?(cycles = Map.empty (module St)) r =
  let r' =
    List.filter_map r ~f:(fun a ->
        match a with
        | IntAtom _ | BoolAtom _ | LabelStubAtom _ | ExprStubAtom _ | FunAtom _
          ->
            Some [ a ]
        | OpAtom op -> (
            match op with
            | PlusOp (r1, r2) | MinusOp (r1, r2) ->
                (* TODO: if either r1/r2 is stub, see if there's | upstream *)
                let int_op =
                  match op with
                  | PlusOp _ -> ( + )
                  | MinusOp _ -> ( - )
                  | _ -> raise Unreachable
                in
                Some
                  (match (r1, r2) with
                  | [ IntAtom i1 ], [ IntAtom i2 ] -> [ IntAtom (int_op i1 i2) ]
                  (* associative *)
                  | [ IntAtom i1 ], [ OpAtom op2 ] ->
                      [
                        OpAtom
                          (match op2 with
                          | PlusOp ([ IntAtom i2 ], r2) -> (
                              (* flip operators accordingly *)
                              match op with
                              | MinusOp _ ->
                                  (* 1 - (2 + 3) => (1 - 2) - 3  *)
                                  MinusOp
                                    ( [
                                        OpAtom
                                          (MinusOp
                                             ([ IntAtom i1 ], [ IntAtom i2 ]));
                                      ],
                                      r2 )
                              | PlusOp _ ->
                                  (* 1 + (2 + 3) => (1 + 2) + 3  *)
                                  PlusOp
                                    ( [
                                        OpAtom
                                          (PlusOp
                                             ([ IntAtom i1 ], [ IntAtom i2 ]));
                                      ],
                                      r2 )
                              | _ -> raise Unreachable)
                          | MinusOp ([ IntAtom i2 ], r2) -> (
                              match op with
                              | MinusOp _ ->
                                  (* 1 - (2 - 3) => (1 - 2) + 3  *)
                                  PlusOp
                                    ( [
                                        OpAtom
                                          (MinusOp
                                             ([ IntAtom i1 ], [ IntAtom i2 ]));
                                      ],
                                      r2 )
                              | PlusOp _ ->
                                  (* 1 + (2 - 3) => (1 + 2) - 3  *)
                                  MinusOp
                                    ( [
                                        OpAtom
                                          (PlusOp
                                             ([ IntAtom i1 ], [ IntAtom i2 ]));
                                      ],
                                      r2 )
                              | _ -> raise Unreachable)
                          | _ -> (
                              (* don't proceed in cases like 1 + (2 * 3) *)
                              let r1', r2' =
                                (simplify r1 ~cycles, simplify r2 ~cycles)
                              in
                              match op with
                              | PlusOp _ -> PlusOp (r1', r2')
                              | MinusOp _ -> MinusOp (r1', r2')
                              | _ -> raise Unreachable));
                      ]
                  (* commutative *)
                  (* | r1, [ OpAtom (PlusOp (r2, [ IntAtom i2 ])) ] ->
                      OpAtom
                        (PlusOp (r1, [ OpAtom (PlusOp ([ IntAtom i2 ], r2)) ])) *)
                  | [ IntAtom i1 ], [ LabelResAtom ([ IntAtom i2 ], st) ]
                  | [ LabelResAtom ([ IntAtom i1 ], st) ], [ IntAtom i2 ] ->
                      [ LabelResAtom ([ IntAtom (int_op i1 i2) ], st) ]
                  (* this case should be very rare *)
                  | [ PathCondAtom (pc1, r1) ], [ PathCondAtom (pc2, r2) ]
                    when Stdlib.(pc1 = pc2) ->
                      [
                        PathCondAtom
                          ( pc1,
                            [
                              OpAtom
                                (match op with
                                | PlusOp _ -> PlusOp (r1, r2)
                                | MinusOp _ -> MinusOp (r1, r2)
                                | MultOp _ -> MultOp (r1, r2)
                                | _ -> raise Unreachable);
                            ] );
                      ]
                  | [ LabelResAtom (r1, st1) ], [ LabelResAtom (r2, st2) ]
                    when Stdlib.(st1 = st2) ->
                      [
                        LabelResAtom
                          ( [
                              OpAtom
                                (match op with
                                | PlusOp _ -> PlusOp (r1, r2)
                                | MinusOp _ -> MinusOp (r1, r2)
                                | _ -> raise Unreachable);
                            ],
                            st1 );
                      ]
                  | ( [ ExprResAtom (r1, ((e1, _) as st1)) ],
                      [ ExprResAtom (r2, (e2, _)) ] )
                    when Stdlib.(e1 = e2) ->
                      [
                        ExprResAtom
                          ( [
                              OpAtom
                                (match op with
                                | PlusOp _ -> PlusOp (r1, r2)
                                | MinusOp _ -> MinusOp (r1, r2)
                                | _ -> raise Unreachable);
                            ],
                            st1 );
                      ]
                  | [ IntAtom _ ], [ LabelResAtom (r, st) ] ->
                      [
                        LabelResAtom
                          ( List.map r ~f:(function
                              | PathCondAtom (pc, r) ->
                                  PathCondAtom
                                    ( pc,
                                      [
                                        OpAtom
                                          (match op with
                                          | PlusOp _ -> PlusOp (r1, r)
                                          | MinusOp _ -> MinusOp (r1, r)
                                          | _ -> raise Unreachable);
                                      ] )
                              | _ as a -> a (* failwith "distributive" *)),
                            st );
                      ]
                  | _ ->
                      let r1', r2' =
                        (simplify r1 ~cycles, simplify r2 ~cycles)
                      in
                      [
                        OpAtom
                          (match op with
                          | PlusOp _ -> PlusOp (r1', r2')
                          | MinusOp _ -> MinusOp (r1', r2')
                          | _ -> raise Unreachable);
                      ])
            | MultOp (r1, r2) -> (
                match (r1, r2) with
                | [ IntAtom i1 ], [ IntAtom i2 ] -> Some [ IntAtom (i1 * i2) ]
                | [ IntAtom i1 ], [ OpAtom op2 ] -> (
                    match op2 with
                    | MultOp ([ IntAtom i2 ], r2) ->
                        Some [ OpAtom (MultOp ([ IntAtom (i1 * i2) ], r2)) ]
                    | _ -> failwith "TODO: distributive")
                | [ IntAtom i1 ], [ LabelResAtom ([ IntAtom i2 ], st) ]
                | [ LabelResAtom ([ IntAtom i1 ], st) ], [ IntAtom i2 ] ->
                    Some [ LabelResAtom ([ IntAtom (i1 * i2) ], st) ]
                | [ IntAtom i1 ], [ ExprResAtom ([ IntAtom i2 ], st) ]
                | [ ExprResAtom ([ IntAtom i1 ], st) ], [ IntAtom i2 ] ->
                    Some [ ExprResAtom ([ IntAtom (i1 * i2) ], st) ]
                | _ ->
                    Some
                      [
                        OpAtom
                          (MultOp (simplify r1 ~cycles, simplify r2 ~cycles));
                      ])
            | EqualOp (r1, r2)
            | GeOp (r1, r2)
            | GtOp (r1, r2)
            | LeOp (r1, r2)
            | LtOp (r1, r2) -> (
                let int_op =
                  match op with
                  | EqualOp _ -> ( = )
                  | GeOp _ -> ( >= )
                  | GtOp _ -> ( > )
                  | LeOp _ -> ( <= )
                  | LtOp _ -> ( < )
                  | _ -> raise Unreachable
                in
                match (r1, r2) with
                | [ IntAtom i1 ], [ IntAtom i2 ] ->
                    Some [ BoolAtom (int_op i1 i2) ]
                | _ ->
                    let r1', r2' = (simplify r1 ~cycles, simplify r2 ~cycles) in
                    Some
                      [
                        OpAtom
                          (match op with
                          | EqualOp _ -> EqualOp (r1', r2')
                          | GeOp _ -> GeOp (r1', r2')
                          | GtOp _ -> GtOp (r1', r2')
                          | LeOp _ -> LeOp (r1', r2')
                          | LtOp _ -> LtOp (r1', r2')
                          | _ -> raise Unreachable);
                      ])
            | AndOp (r1, r2) | OrOp (r1, r2) -> (
                let bool_op =
                  match op with
                  | AndOp _ -> ( && )
                  | OrOp _ -> ( || )
                  | _ -> raise Unreachable
                in
                match (r1, r2) with
                | [ BoolAtom b1 ], [ BoolAtom b2 ] ->
                    Some [ BoolAtom (bool_op b1 b2) ]
                | _ ->
                    let r1', r2' = (simplify r1 ~cycles, simplify r2 ~cycles) in
                    Some
                      [
                        OpAtom
                          (match op with
                          | AndOp _ -> AndOp (r1', r2')
                          | OrOp _ -> OrOp (r1', r2')
                          | _ -> raise Unreachable);
                      ])
            | NotOp r -> (
                match r with
                | [ BoolAtom b ] -> Some [ BoolAtom (not b) ]
                | _ ->
                    let r' = simplify r ~cycles in
                    Some [ OpAtom (NotOp r') ]))
        | AssertAtom (id, r, rv) ->
            Some [ AssertAtom (id, simplify r ~cycles, rv) ]
        | LabelResAtom (r, st) -> (
            (* let cycles = Map.add_exn cycles ~key:(State.Lstate st, 0) ~data:r in *)
            match r with
            | [] -> None
            | _ when not (has_stub r (St.Lstate st)) -> Some r
            | _ -> Some [ LabelResAtom (simplify r ~cycles, st) ])
        | ExprResAtom (r, st) -> (
            (* let cycles = Map.add_exn cycles ~key:(State.Estate st, 0) ~data:r in *)
            match r with
            | [] -> None
            | _ when not (has_stub r (St.Estate st)) -> Some r
            | _ -> Some [ ExprResAtom (simplify r ~cycles, st) ])
        | PathCondAtom ((r_cond, b), r) -> (
            match r_cond with
            | [ BoolAtom b' ] when Bool.(b' = b) ->
                Some [ LabelResAtom (r, (0, [])) ]
            | _ ->
                Some
                  [
                    PathCondAtom
                      ((simplify r_cond ~cycles, b), simplify r ~cycles);
                  ])
        | RecordAtom entries ->
            Some
              [
                RecordAtom
                  (List.map entries ~f:(fun (id, r) -> (id, simplify r ~cycles)));
              ]
        | ProjectionAtom (r, x) -> (
            match r with
            | [ RecordAtom entries ] -> (
                match List.find entries ~f:(fun (id, _) -> Stdlib.(id = x)) with
                | Some (_, r) -> Some [ LabelResAtom (r, (0, [])) ]
                | None -> failwith "runtime error")
            (* | [ ExprStubAtom st ] -> (
                match Map.find cycles (State.Estate st, 0) with
                | Some r when List.length r > 1 -> (
                    match r with
                    | [ RecordAtom entries; ExprStubAtom _ ] ->
                        Logs.info (fun m -> m "%a" pp_res r);
                        failwith "yo"
                    | _ -> ProjectionAtom (simplify  r ~cycles, x))
                | _ ->
                    (* Map.iteri cycles ~f:(fun ~key:(st, _) ~data ->
                        Format.printf "%s\n" (State.show_state st)); *)
                    ProjectionAtom (simplify  r ~cycles, x)) *)
            | _ ->
                (* Logs.info (fun m -> m "%a" Utils.pp_atom a);
                   Logs.info (fun m -> m "%a" pp_atom a);
                   Logs.info (fun m -> m "cycles:"); *)
                (* Map.iteri cycles ~f:(fun ~key:(st, _) ~data ->
                    Logs.info (fun m ->
                        m "%s -> %a\n" (State.show_state st) Utils.pp_res data)); *)
                Some [ ProjectionAtom (simplify r ~cycles, x) ])
        | InspectionAtom (x, r) -> (
            match r with
            | [ RecordAtom entries ] ->
                Some
                  [
                    BoolAtom
                      (List.exists entries ~f:(fun (id, _) -> Stdlib.(id = x)));
                  ]
            | _ -> Some [ InspectionAtom (x, simplify r ~cycles) ])
        (* | _ -> failwith "unimplemented" *))
  in
  (* Format.printf "r: %a\n" Utils.pp_res r;
     Format.printf "r': %a\n" Utils.pp_res r'; *)
  (* let r' =
       match r' with
       | [
        FunAtom (e1, l1, _);
        FunAtom (e2, l2, sigma2);
       ]
         when Stdlib.(e1 = e2) && l1 = l2 ->
           [ ExprResAtom (r1 @ r2, (Var (id1, l1), sigma2)) ]
       | _ -> r'
     in *)
  let r' = List.concat r' in
  if compare_res r r' = 0 then r' else simplify r' ~cycles
