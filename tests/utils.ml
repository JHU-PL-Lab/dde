let rec strip_label (e : Ddeast.expr) : Fbast.expr =
  match e with
  | Ddeast.Int (i, label) -> Fbast.Int i
  | Ddeast.Function (Ddeast.Ident x, e, label) ->
      Fbast.Function (Fbast.Ident x, strip_label e)
  | Ddeast.Bool (b, label) -> Fbast.Bool b
  | Ddeast.Appl (e1, e2, label) -> Fbast.Appl (strip_label e1, strip_label e2)
  | Ddeast.Var (Ident x, label) -> Fbast.Var (Fbast.Ident x)
  | Ddeast.Plus (e1, e2, label) -> Fbast.Plus (strip_label e1, strip_label e2)
  | Ddeast.Minus (e1, e2, label) -> Fbast.Minus (strip_label e1, strip_label e2)
  | Ddeast.Equal (e1, e2, label) -> Fbast.Equal (strip_label e1, strip_label e2)
  | Ddeast.And (e1, e2, label) -> Fbast.And (strip_label e1, strip_label e2)
  | Ddeast.Or (e1, e2, label) -> Fbast.Or (strip_label e1, strip_label e2)
  | Ddeast.Not (e, label) -> Fbast.Not (strip_label e)
  | Ddeast.If (e1, e2, e3, label) ->
      Fbast.If (strip_label e1, strip_label e2, strip_label e3)
  | _ -> failwith "unreachable"

let dde_eval s =
  Lexing.from_string s
  |> Ddeparser.main Ddelexer.token
  |> Ddeinterp.eval false |> strip_label

let dde_parse s =
  s ^ ";;" |> Lexing.from_string |> Ddeparser.main Ddelexer.token |> strip_label

let fb_eval s =
  Lexing.from_string s |> Fbparser.main Fblexer.token |> Fbinterp.eval

let dde_pp e = Format.printf "%a\n" Ddepp.pp_expr e
let fb_pp e = Format.printf "%a\n" Fbpp.pp_expr e
let assert_unequal e1 e2 = OUnit2.assert_equal ~cmp:(fun a b -> a <> b) e1 e2
