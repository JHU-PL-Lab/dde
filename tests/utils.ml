exception Unreachable

let rec strip_label_fb (e : Ddeast.expr) : Fbast.expr =
  match e with
  | Value value -> (
      match value with
      | Int i -> Int i
      | Bool b -> Bool b
      | Function (Ident x, e, _) -> Function (Ident x, strip_label_fb e))
  | Appl (e1, e2, _) -> Appl (strip_label_fb e1, strip_label_fb e2)
  | Var (Ident x, _) -> Var (Ident x)
  | Plus (e1, e2, _) -> Plus (strip_label_fb e1, strip_label_fb e2)
  | Minus (e1, e2, _) -> Minus (strip_label_fb e1, strip_label_fb e2)
  | Equal (e1, e2, _) -> Equal (strip_label_fb e1, strip_label_fb e2)
  | And (e1, e2, _) -> And (strip_label_fb e1, strip_label_fb e2)
  | Or (e1, e2, _) -> Or (strip_label_fb e1, strip_label_fb e2)
  | Not (e, _) -> Not (strip_label_fb e)
  | If (e1, e2, e3, _) ->
      If (strip_label_fb e1, strip_label_fb e2, strip_label_fb e3)
  | _ -> raise Unreachable

let rec strip_label_fbenv (e : Ddeast.expr) : Fbenvast.expr =
  match e with
  | Value value -> (
      match value with
      | Int i -> Int i
      | Bool b -> Bool b
      | Function (Ident x, e, _) -> Function (Ident x, strip_label_fbenv e))
  | Appl (e1, e2, _) -> Appl (strip_label_fbenv e1, strip_label_fbenv e2)
  | Var (Ident x, _) -> Var (Ident x)
  | Plus (e1, e2, _) -> Plus (strip_label_fbenv e1, strip_label_fbenv e2)
  | Minus (e1, e2, _) -> Minus (strip_label_fbenv e1, strip_label_fbenv e2)
  | Equal (e1, e2, _) -> Equal (strip_label_fbenv e1, strip_label_fbenv e2)
  | And (e1, e2, _) -> And (strip_label_fbenv e1, strip_label_fbenv e2)
  | Or (e1, e2, _) -> Or (strip_label_fbenv e1, strip_label_fbenv e2)
  | Not (e, _) -> Not (strip_label_fbenv e)
  | If (e1, e2, e3, _) ->
      If (strip_label_fbenv e1, strip_label_fbenv e2, strip_label_fbenv e3)
  | _ -> raise Unreachable

let dde_to_fb (v : Ddeinterp.result_value) : Fbast.expr =
  match v with
  | IntResult i -> Int i
  | BoolResult b -> Bool b
  | FunctionResult { f; l; sigma } -> (
      match f with
      | Function (Ident x, le, _) -> Function (Ident x, strip_label_fb le)
      | _ -> raise Unreachable)
  | _ -> raise Unreachable

let dde_to_fbenv (v : Ddeinterp.result_value) : Fbenvast.expr =
  match v with
  | IntResult i -> Int i
  | BoolResult b -> Bool b
  | FunctionResult { f; l; sigma } -> (
      match f with
      | Function (Ident x, le, _) -> Function (Ident x, strip_label_fbenv le)
      | _ -> raise Unreachable)
  | _ -> raise Unreachable

let dde_eval_fb s =
  Lexing.from_string s
  |> Ddeparser.main Ddelexer.token
  |> Ddeinterp.eval false |> dde_to_fb

let dde_eval_fbenv s =
  Lexing.from_string s
  |> Ddeparser.main Ddelexer.token
  |> Ddeinterp.eval false |> dde_to_fbenv

let dde_parse s =
  s ^ ";;" |> Lexing.from_string
  |> Ddeparser.main Ddelexer.token
  |> strip_label_fb

let fb_eval s =
  Lexing.from_string s |> Fbparser.main Fblexer.token |> Fbinterp.eval

let fbenv_eval s =
  Lexing.from_string s |> Fbenvparser.main Fbenvlexer.token |> Fbenvinterp.eval

let dde_pp e = Format.printf "%a\n" Ddepp.pp_expr e
let fb_pp e = Format.printf "%a\n" Fbpp.pp_expr e
let assert_unequal e1 e2 = OUnit2.assert_equal ~cmp:(fun a b -> a <> b) e1 e2
