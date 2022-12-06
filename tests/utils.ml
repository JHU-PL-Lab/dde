exception Unreachable

let rec strip_label le =
  let e, _ = le in
  match e with
  | Ddeast.Int i -> Fbast.Int i
  | Ddeast.Function (Ddeast.Ident x, e) ->
      Fbast.Function (Fbast.Ident x, strip_label e)
  | Ddeast.Bool b -> Fbast.Bool b
  | Ddeast.Appl (e1, e2) -> Fbast.Appl (strip_label e1, strip_label e2)
  | Ddeast.Var (Ident x) -> Fbast.Var (Fbast.Ident x)
  | Ddeast.Plus (e1, e2) -> Fbast.Plus (strip_label e1, strip_label e2)
  | Ddeast.Minus (e1, e2) -> Fbast.Minus (strip_label e1, strip_label e2)
  | Ddeast.Equal (e1, e2) -> Fbast.Equal (strip_label e1, strip_label e2)
  | Ddeast.And (e1, e2) -> Fbast.And (strip_label e1, strip_label e2)
  | Ddeast.Or (e1, e2) -> Fbast.Or (strip_label e1, strip_label e2)
  | Ddeast.Not e -> Fbast.Not (strip_label e)
  | Ddeast.If (e1, e2, e3) ->
      Fbast.If (strip_label e1, strip_label e2, strip_label e3)
  | _ -> raise Unreachable

let dde_eval s =
  Lexing.from_string s
  |> Ddeparser.main Ddelexer.token
  |> Ddeinterp.eval false |> strip_label

let dde_parse s =
  s ^ ";;" |> Lexing.from_string |> Ddeparser.main Ddelexer.token |> strip_label

let fb_eval s =
  Lexing.from_string s |> Fbparser.main Fblexer.token |> Fbinterp.eval

let dde_pp e = Format.printf "%a\n" Ddepp.pp_lexpr e
let fb_pp e = Format.printf "%a\n" Fbpp.pp_expr e
let assert_unequal e1 e2 = OUnit2.assert_equal ~cmp:(fun a b -> a <> b) e1 e2
