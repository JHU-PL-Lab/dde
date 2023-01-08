open Lib

let ff = Format.fprintf

let rec pp_result_value fmt (v : result_value) =
  match v with
  | IntResult x -> ff fmt "%d" x
  | BoolResult b -> ff fmt "%b" b
  | FunResult { f; l; sigma } -> (
      match f with
      | Function (Ident i, le, l) ->
          ff fmt "(@[<hv>function %s ->@;<1 4>%a@])^%d" i Ddepp.pp_expr le l
      | _ -> raise Unreachable)
  | ChoiceResult { ls; l; sigma } ->
      ff fmt "(%s)^%d"
        (List.fold_left
           (fun acc r -> acc ^ " | " ^ Format.asprintf "%a" pp_result_value r)
           "" ls)
        l
  | OpResult op -> (
      match op with
      | PlusOp (r1, r2) ->
          ff fmt "(%a + %a)" pp_result_value r1 pp_result_value r2
      | MinusOp (r1, r2) ->
          ff fmt "(%a - %a)" pp_result_value r1 pp_result_value r2
      | EqualOp (r1, r2) ->
          ff fmt "(%a = %a)" pp_result_value r1 pp_result_value r2
      | AndOp (r1, r2) ->
          ff fmt "(%a and %a)" pp_result_value r1 pp_result_value r2
      | OrOp (r1, r2) ->
          ff fmt "(%a or %a)" pp_result_value r1 pp_result_value r2
      | NotOp r1 -> ff fmt "(not %a)" pp_result_value r1)
  | _ -> failwith "unimplemented"
