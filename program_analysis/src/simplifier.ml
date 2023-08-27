open Core
open Grammar
open Option.Let_syntax

exception Unreachable

let rec has_stub r st =
  List.exists r ~f:(function
    | IntAtom _ | BoolAtom _ | FunAtom _ -> false
    | LabelStubAtom lst -> Stdlib.(State.Lstate lst = st)
    | ExprStubAtom est -> Stdlib.(State.Estate est = st)
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
        (not Stdlib.(State.Lstate st' = st)) && has_stub r st
    | ExprResAtom (r, st') ->
        (not Stdlib.(State.Estate st' = st)) && has_stub r st
    | PathCondAtom (_, r) -> has_stub r st
    | RecordAtom entries -> List.exists entries ~f:(fun (_, r) -> has_stub r st)
    | ProjectionAtom (r, _) -> has_stub r st
    | InspectionAtom (_, r) -> has_stub r st
    | AssertAtom (_, r, _) -> has_stub r st)

let rec extract_fun r =
  match r with
  | a :: r' -> (
      match a with
      | FunAtom _ -> Some a
      | LabelResAtom (r, _) | ExprResAtom (r, _) | PathCondAtom (_, r) -> (
          match extract_fun r with Some f -> Some f | None -> extract_fun r')
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
          | OrOp (r1, r2) -> (
              match extract_fun r1 with
              | Some f -> Some f
              | None -> (
                  match extract_fun r2 with
                  | Some f -> Some f
                  | None -> extract_fun r'))
          | NotOp r -> (
              match extract_fun r with
              | Some f -> Some f
              | None -> extract_fun r'))
      | IntAtom _ | BoolAtom _ | LabelStubAtom _ | ExprStubAtom _ ->
          extract_fun r'
      | _ -> failwith "unimplemented")
  | [] -> None

let rec simplify r =
  let r' =
    List.map r ~f:(fun a ->
        match a with
        | IntAtom _ | BoolAtom _ | LabelStubAtom _ | ExprStubAtom _ | FunAtom _
          ->
            a
        | OpAtom op -> (
            match op with
            | PlusOp (r1, r2) | MinusOp (r1, r2) -> (
                let int_op =
                  match op with
                  | PlusOp _ -> ( + )
                  | MinusOp _ -> ( - )
                  | _ -> raise Unreachable
                in
                match (r1, r2) with
                | [ IntAtom i1 ], [ IntAtom i2 ] -> IntAtom (int_op i1 i2)
                (* associative *)
                | [ IntAtom i1 ], [ OpAtom op2 ] ->
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
                                      (MinusOp ([ IntAtom i1 ], [ IntAtom i2 ]));
                                  ],
                                  r2 )
                          | PlusOp _ ->
                              (* 1 + (2 + 3) => (1 + 2) + 3  *)
                              PlusOp
                                ( [
                                    OpAtom
                                      (PlusOp ([ IntAtom i1 ], [ IntAtom i2 ]));
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
                                      (MinusOp ([ IntAtom i1 ], [ IntAtom i2 ]));
                                  ],
                                  r2 )
                          | PlusOp _ ->
                              (* 1 + (2 - 3) => (1 + 2) - 3  *)
                              MinusOp
                                ( [
                                    OpAtom
                                      (PlusOp ([ IntAtom i1 ], [ IntAtom i2 ]));
                                  ],
                                  r2 )
                          | _ -> raise Unreachable)
                      | _ -> (
                          (* don't proceed in cases like 1 + (2 * 3) *)
                          let r1', r2' = (simplify r1, simplify r2) in
                          match op with
                          | PlusOp _ -> PlusOp (r1', r2')
                          | MinusOp _ -> MinusOp (r1', r2')
                          | _ -> raise Unreachable))
                (* commutative *)
                (* | r1, [ OpAtom (PlusOp (r2, [ IntAtom i2 ])) ] ->
                    OpAtom
                      (PlusOp (r1, [ OpAtom (PlusOp ([ IntAtom i2 ], r2)) ])) *)
                | [ IntAtom i1 ], [ LabelResAtom ([ IntAtom i2 ], st) ]
                | [ LabelResAtom ([ IntAtom i1 ], st) ], [ IntAtom i2 ] ->
                    LabelResAtom ([ IntAtom (int_op i1 i2) ], st)
                (* this case should be very rare *)
                | [ PathCondAtom (pc1, r1) ], [ PathCondAtom (pc2, r2) ]
                  when Stdlib.(pc1 = pc2) ->
                    (* TODO: talk about only doing one step at a time *)
                    PathCondAtom
                      ( pc1,
                        [
                          OpAtom
                            (match op with
                            | PlusOp _ -> PlusOp (r1, r2)
                            | MinusOp _ -> MinusOp (r1, r2)
                            | MultOp _ -> MultOp (r1, r2)
                            | _ -> raise Unreachable);
                        ] )
                | [ LabelResAtom (r1, st1) ], [ LabelResAtom (r2, st2) ]
                  when Stdlib.(st1 = st2) ->
                    LabelResAtom
                      ( [
                          OpAtom
                            (match op with
                            | PlusOp _ -> PlusOp (r1, r2)
                            | MinusOp _ -> MinusOp (r1, r2)
                            | _ -> raise Unreachable);
                        ],
                        st1 )
                | [ ExprResAtom (r1, st1) ], [ ExprResAtom (r2, st2) ]
                  when Stdlib.(st1 = st2) ->
                    ExprResAtom
                      ( [
                          OpAtom
                            (match op with
                            | PlusOp _ -> PlusOp (r1, r2)
                            | MinusOp _ -> MinusOp (r1, r2)
                            | _ -> raise Unreachable);
                        ],
                        st1 )
                | [ IntAtom _ ], [ LabelResAtom (r, st) ] ->
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
                          | _ as a ->
                              Format.printf "%a" Grammar.pp_atom a;
                              failwith "distributive"),
                        st )
                | _ ->
                    let r1', r2' = (simplify r1, simplify r2) in
                    OpAtom
                      (match op with
                      | PlusOp _ -> PlusOp (r1', r2')
                      | MinusOp _ -> MinusOp (r1', r2')
                      | _ -> raise Unreachable))
            | MultOp (r1, r2) -> (
                match (r1, r2) with
                | [ IntAtom i1 ], [ IntAtom i2 ] -> IntAtom (i1 * i2)
                | [ IntAtom i1 ], [ OpAtom op2 ] -> (
                    match op2 with
                    | MultOp ([ IntAtom i2 ], r2) ->
                        OpAtom (MultOp ([ IntAtom (i1 * i2) ], r2))
                    | _ -> failwith "TODO: distributive")
                | [ IntAtom i1 ], [ LabelResAtom ([ IntAtom i2 ], st) ]
                | [ LabelResAtom ([ IntAtom i1 ], st) ], [ IntAtom i2 ] ->
                    LabelResAtom ([ IntAtom (i1 * i2) ], st)
                | [ IntAtom i1 ], [ ExprResAtom ([ IntAtom i2 ], st) ]
                | [ ExprResAtom ([ IntAtom i1 ], st) ], [ IntAtom i2 ] ->
                    ExprResAtom ([ IntAtom (i1 * i2) ], st)
                | _ -> OpAtom (MultOp (simplify r1, simplify r2)))
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
                | [ IntAtom i1 ], [ IntAtom i2 ] -> BoolAtom (int_op i1 i2)
                | _ ->
                    let r1', r2' = (simplify r1, simplify r2) in
                    OpAtom
                      (match op with
                      | EqualOp _ -> EqualOp (r1', r2')
                      | GeOp _ -> GeOp (r1', r2')
                      | GtOp _ -> GtOp (r1', r2')
                      | LeOp _ -> LeOp (r1', r2')
                      | LtOp _ -> LtOp (r1', r2')
                      | _ -> raise Unreachable))
            | AndOp (r1, r2) | OrOp (r1, r2) -> (
                let bool_op =
                  match op with
                  | AndOp _ -> ( && )
                  | OrOp _ -> ( || )
                  | _ -> raise Unreachable
                in
                match (r1, r2) with
                | [ BoolAtom b1 ], [ BoolAtom b2 ] -> BoolAtom (bool_op b1 b2)
                | _ ->
                    let r1', r2' = (simplify r1, simplify r2) in
                    OpAtom
                      (match op with
                      | AndOp _ -> AndOp (r1', r2')
                      | OrOp _ -> OrOp (r1', r2')
                      | _ -> raise Unreachable))
            | NotOp r -> (
                match r with
                | [ BoolAtom b ] -> BoolAtom (not b)
                | _ ->
                    let r' = simplify r in
                    OpAtom (NotOp r')))
        | AssertAtom (id, r, rv) -> AssertAtom (id, simplify r, rv)
        | LabelResAtom (r, st) -> (
            match r with
            | [ a ] when not (has_stub r (State.Lstate st)) -> a
            | _ -> (
                match extract_fun r with
                | Some f -> f
                | _ -> LabelResAtom (simplify r, st)))
        | ExprResAtom (r, st) -> (
            match r with
            | [ a ] when not (has_stub r (State.Estate st)) -> a
            | _ -> (
                match extract_fun r with
                | Some f -> f
                | _ -> ExprResAtom (simplify r, st)))
        | PathCondAtom ((r_cond, b), r) -> (
            match r_cond with
            | [ BoolAtom b' ] when Bool.(b' = b) -> LabelResAtom (r, (0, []))
            | _ -> PathCondAtom ((simplify r_cond, b), simplify r))
        | RecordAtom entries ->
            RecordAtom (List.map entries ~f:(fun (id, r) -> (id, simplify r)))
        | ProjectionAtom (r, x) -> (
            match r with
            | [ RecordAtom entries ] -> (
                match List.find entries ~f:(fun (id, _) -> Stdlib.(id = x)) with
                | Some (_, r) -> LabelResAtom (r, (0, []))
                | None -> failwith "runtime error")
            | _ -> ProjectionAtom (simplify r, x))
        | InspectionAtom (x, r) -> (
            match r with
            | [ RecordAtom entries ] ->
                BoolAtom
                  (List.exists entries ~f:(fun (id, _) -> Stdlib.(id = x)))
            | _ -> InspectionAtom (x, simplify r)))
  in
  (* Format.printf "r: %a\n" Utils.pp_res r;
     Format.printf "r': %a\n" Utils.pp_res r'; *)
  if Stdlib.(r' = r) then r' else simplify r'
