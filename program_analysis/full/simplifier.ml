(** Simplification of results of full analysis per paper Section 5.2.1 *)

open Core
open Interp.Ast
open Utils
open Utils.Atom
open Exns
open Logs

(* TODO: Break into two *)

(** Recursively checks if any disjunct in result `r` has
    a stub with `label` *)
let rec exists_stub label r =
  List.exists r ~f:(function
    | FunAtom _ | IntAtom _ | BoolAtom _ -> false
    | LStubAtom st -> St.(label = St.Lstate st)
    | EStubAtom st -> St.(label = St.Estate st)
    | RecAtom entries ->
        List.exists entries ~f:(fun (_, r) -> exists_stub label r)
    | ProjAtom (r, _)
    | InspAtom (_, r)
    | LResAtom (r, _)
    | EResAtom (r, _)
    | PathCondAtom (_, r)
    | AssertAtom (_, r, _)
    | NotAtom r ->
        exists_stub label r
    | PlusAtom (r1, r2)
    | MinusAtom (r1, r2)
    | MultAtom (r1, r2)
    | EqAtom (r1, r2)
    | GeAtom (r1, r2)
    | GtAtom (r1, r2)
    | LeAtom (r1, r2)
    | LtAtom (r1, r2)
    | AndAtom (r1, r2)
    | OrAtom (r1, r2) ->
        exists_stub label r1 || exists_stub label r2)

(** Removes stubs without a parent - lone stubs that don't form a cycle *)
let elim_stub label r =
  if exists_stub label r then
    let bases =
      List.filter_map r ~f:(fun a ->
          match a with
          | RecAtom _ when not (exists_stub label [ a ]) -> Some a
          | ProjAtom (([ RecAtom es ] as r), Ident key)
            when not (exists_stub label r) -> (
              match
                List.find es ~f:(fun (Ident key', _) -> String.(key = key'))
              with
              | Some (_, [ a ]) -> Some a
              | _ ->
                  raise
                    (Runtime_error
                       (Format.sprintf "Missing key %s in record" key)))
          | FunAtom _ -> Some a
          | _ -> None)
    in
    let r' =
      List.concat_map r ~f:(function
        | ProjAtom ([ EStubAtom st ], Ident key) when St.(label = Estate st) ->
            List.concat_map bases ~f:(fun base ->
                match base with
                | RecAtom es -> (
                    match
                      List.find es ~f:(fun (Ident key', _) ->
                          String.(key = key'))
                    with
                    | Some (_, r) -> r
                    (* TODO: Raise instead? *)
                    | None -> [])
                | _ -> raise (Runtime_error "Missing stub parent"))
        | EStubAtom st when St.(label = Estate st) -> []
        (* | LStubAtom st when St.(label = Lstate st) -> [] *)
        | a -> [ a ])
    in
    r'
  else r

let int_arith_op = function
  | PlusAtom _ -> ( + )
  | MinusAtom _ -> ( - )
  | _ -> raise Unreachable

let int_cmp_op = function
  | EqAtom _ -> ( = )
  | GeAtom _ -> ( >= )
  | GtAtom _ -> ( > )
  | LeAtom _ -> ( <= )
  | LtAtom _ -> ( < )
  | _ -> raise Unreachable

let bool_op = function
  | AndAtom _ -> ( && )
  | OrAtom _ -> ( || )
  | _ -> raise Unreachable

(** Performs simplifications as specified in paper Section 5.2.1 *)
let rec simplify ?(pa = None) r =
  let r' =
    List.filter_map r ~f:(fun a ->
        match a with
        | IntAtom _ | BoolAtom _ | LStubAtom _ | EStubAtom _ | FunAtom _ ->
            Some [ a ]
        | PlusAtom (r1, r2) | MinusAtom (r1, r2) ->
            Some
              (match (r1, r2) with
              | [ IntAtom i1 ], [ IntAtom i2 ] ->
                  [ IntAtom (int_arith_op a i1 i2) ]
              (* associative *)
              | [ IntAtom i1 ], [ PlusAtom ([ IntAtom i2 ], r2) ] ->
                  [
                    (* flip operators accordingly *)
                    (match a with
                    | MinusAtom _ ->
                        (* e.g., 1 - (2 + 3) => (1 - 2) - 3  *)
                        MinusAtom
                          ([ MinusAtom ([ IntAtom i1 ], [ IntAtom i2 ]) ], r2)
                    | PlusAtom _ ->
                        (* e.g., 1 + (2 + 3) => (1 + 2) + 3  *)
                        PlusAtom
                          ([ PlusAtom ([ IntAtom i1 ], [ IntAtom i2 ]) ], r2)
                    | _ -> raise Unreachable);
                  ]
              | [ IntAtom i1 ], [ MinusAtom ([ IntAtom i2 ], r2) ] ->
                  [
                    (match a with
                    | MinusAtom _ ->
                        (* e.g., 1 - (2 - 3) => (1 - 2) + 3  *)
                        PlusAtom
                          ([ MinusAtom ([ IntAtom i1 ], [ IntAtom i2 ]) ], r2)
                    | PlusAtom _ ->
                        (* e.g., 1 + (2 - 3) => (1 + 2) - 3  *)
                        MinusAtom
                          ([ PlusAtom ([ IntAtom i1 ], [ IntAtom i2 ]) ], r2)
                    | _ -> raise Unreachable);
                  ]
              (* this case should be very rare *)
              | [ PathCondAtom (pc1, r1) ], [ PathCondAtom (pc2, r2) ]
                when Stdlib.(pc1 = pc2) ->
                  [
                    PathCondAtom
                      ( pc1,
                        [
                          (match a with
                          | PlusAtom _ -> PlusAtom (r1, r2)
                          | MinusAtom _ -> MinusAtom (r1, r2)
                          | MultAtom _ -> MultAtom (r1, r2)
                          | _ -> raise Unreachable);
                        ] );
                  ]
              | [ IntAtom i ], [ PathCondAtom (pc, r) ]
              | [ PathCondAtom (pc, r) ], [ IntAtom i ] ->
                  [
                    PathCondAtom
                      ( pc,
                        List.map r ~f:(function
                          | IntAtom i' -> IntAtom (int_arith_op a i i')
                          | a' -> (
                              match a with
                              | PlusAtom _ -> PlusAtom ([ IntAtom i ], [ a' ])
                              | MinusAtom _ -> MinusAtom ([ IntAtom i ], [ a' ])
                              | _ -> raise Unreachable)) );
                  ]
              | [ LResAtom (r1, st1) ], [ LResAtom (r2, st2) ]
                when Stdlib.(st1 = st2) ->
                  [
                    LResAtom
                      ( [
                          (match a with
                          | PlusAtom _ -> PlusAtom (r1, r2)
                          | MinusAtom _ -> MinusAtom (r1, r2)
                          | _ -> raise Unreachable);
                        ],
                        st1 );
                  ]
              | [ EResAtom (r1, ((e1, _) as st1)) ], [ EResAtom (r2, (e2, _)) ]
                when Stdlib.(e1 = e2) ->
                  [
                    EResAtom
                      ( [
                          (match a with
                          | PlusAtom _ -> PlusAtom (r1, r2)
                          | MinusAtom _ -> MinusAtom (r1, r2)
                          | _ -> raise Unreachable);
                        ],
                        st1 );
                  ]
              | [ IntAtom i ], r ->
                  List.map r ~f:(function
                    | IntAtom i' -> IntAtom (int_arith_op a i i')
                    | a' -> (
                        match a with
                        | PlusAtom _ -> PlusAtom ([ IntAtom i ], [ a' ])
                        | MinusAtom _ -> MinusAtom ([ IntAtom i ], [ a' ])
                        | _ -> raise Unreachable))
              | r, [ IntAtom i ] ->
                  List.map r ~f:(function
                    | IntAtom i' -> IntAtom (int_arith_op a i' i)
                    | a' -> (
                        match a with
                        | PlusAtom _ -> PlusAtom ([ a' ], [ IntAtom i ])
                        | MinusAtom _ -> MinusAtom ([ a' ], [ IntAtom i ])
                        | _ -> raise Unreachable))
              | _ ->
                  let r1', r2' =
                    (simplify r1 ~pa:(Some a), simplify r2 ~pa:(Some a))
                  in
                  [
                    (match a with
                    | PlusAtom _ -> PlusAtom (r1', r2')
                    | MinusAtom _ -> MinusAtom (r1', r2')
                    | _ -> raise Unreachable);
                  ])
        | MultAtom (r1, r2) -> (
            match (r1, r2) with
            | [ IntAtom i1 ], [ IntAtom i2 ] -> Some [ IntAtom (i1 * i2) ]
            | [ IntAtom i1 ], [ MultAtom ([ IntAtom i2 ], r2) ] ->
                Some [ MultAtom ([ IntAtom (i1 * i2) ], r2) ]
            | [ IntAtom i1 ], [ EResAtom ([ IntAtom i2 ], st) ]
            | [ EResAtom ([ IntAtom i1 ], st) ], [ IntAtom i2 ] ->
                Some [ EResAtom ([ IntAtom (i1 * i2) ], st) ]
            | _ ->
                Some
                  [
                    MultAtom (simplify r1 ~pa:(Some a), simplify r2 ~pa:(Some a));
                  ])
        | EqAtom (r1, r2)
        | GeAtom (r1, r2)
        | GtAtom (r1, r2)
        | LeAtom (r1, r2)
        | LtAtom (r1, r2) -> (
            match (r1, r2) with
            | [ IntAtom i1 ], [ IntAtom i2 ] ->
                Some [ BoolAtom (int_cmp_op a i1 i2) ]
            | _ ->
                let r1', r2' =
                  (simplify r1 ~pa:(Some a), simplify r2 ~pa:(Some a))
                in
                Some
                  [
                    (match a with
                    | EqAtom _ -> EqAtom (r1', r2')
                    | GeAtom _ -> GeAtom (r1', r2')
                    | GtAtom _ -> GtAtom (r1', r2')
                    | LeAtom _ -> LeAtom (r1', r2')
                    | LtAtom _ -> LtAtom (r1', r2')
                    | _ -> raise Unreachable);
                  ])
        | AndAtom (r1, r2) | OrAtom (r1, r2) ->
            Some
              (List.concat_map r1 ~f:(fun a1 ->
                   List.map r2 ~f:(fun a2 ->
                       match (a1, a2) with
                       | BoolAtom b1, BoolAtom b2 -> BoolAtom (bool_op a b1 b2)
                       | _ -> (
                           let r1' = simplify r1 ~pa:(Some a) in
                           let r2' = simplify r2 ~pa:(Some a) in
                           match a with
                           | AndAtom _ -> AndAtom (r1', r2')
                           | OrAtom _ -> OrAtom (r1', r2')
                           | _ -> raise Unreachable))))
        | NotAtom r -> (
            match r with
            | [ BoolAtom b ] -> Some [ BoolAtom (not b) ]
            | _ ->
                let r' = simplify r ~pa:(Some a) in
                Some [ NotAtom r' ])
        | AssertAtom (id, r, rv) ->
            Some [ AssertAtom (id, simplify r ~pa:(Some a), rv) ]
        | LResAtom (r, st) -> (
            match r with
            | [] -> None
            | _ when not (exists_stub r (St.Lstate st)) -> Some r
            | _ -> Some [ LResAtom (simplify r ~pa:(Some a), st) ])
        | EResAtom (r, st) -> (
            match r with
            | [] -> None
            | _ when not (exists_stub r (St.Estate st)) -> Some r
            | _ -> Some [ EResAtom (simplify r ~pa:(Some a), st) ])
        | PathCondAtom ((r_cond, b), r) ->
            if
              List.exists r_cond ~f:(function
                | BoolAtom b' -> Bool.(b = b')
                | _ -> false)
            then Some r
            else
              Some
                [
                  PathCondAtom
                    ((simplify r_cond ~pa:(Some a), b), simplify r ~pa:(Some a));
                ]
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
                       | None -> [])
                   | _ -> [ ProjAtom ([ a ], id) ]))
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
  (* Stops when there's no change to the input result *)
  if Res.compare r r' = 0 then r' else simplify r' ~pa
