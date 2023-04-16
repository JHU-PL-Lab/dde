open Interpreter
open Lib

let ff = Format.fprintf

let rec pp_result_value fmt (v : result_value) =
  match v with
  | IntResult x -> ff fmt "%d" x
  | BoolResult b -> ff fmt "%b" b
  | FunResult { f; _ } -> (
      match f with
      | Function (Ident i, le, _) ->
          ff fmt "@[<hv>function %s ->@;<1 4>%a@]" i Pp.pp_expr le
      | _ -> raise Unreachable)
  | ChoiceResult { choices; _ } ->
      if List.length choices = 1 then
        ff fmt "| %a" pp_result_value (List.hd choices)
      else
        ff fmt "(%s)"
          (choices
          |> List.map (fun res -> Format.asprintf "%a" pp_result_value res)
          |> String.concat " | ")
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
  | StubResult { l; _ } -> ff fmt "stub_%d" l
