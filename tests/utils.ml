exception Unreachable

let rec strip_label_subst (le : Ddeast.lexpr) : Fbast.expr =
  let e, _ = le in
  match e with
  | Int i -> Int i
  | Function (Ident x, e) -> Function (Ident x, strip_label_subst e)
  | Bool b -> Bool b
  | Appl (e1, e2) -> Appl (strip_label_subst e1, strip_label_subst e2)
  | Var (Ident x) -> Var (Ident x)
  | Plus (e1, e2) -> Plus (strip_label_subst e1, strip_label_subst e2)
  | Minus (e1, e2) -> Minus (strip_label_subst e1, strip_label_subst e2)
  | Equal (e1, e2) -> Equal (strip_label_subst e1, strip_label_subst e2)
  | And (e1, e2) -> And (strip_label_subst e1, strip_label_subst e2)
  | Or (e1, e2) -> Or (strip_label_subst e1, strip_label_subst e2)
  | Not e -> Not (strip_label_subst e)
  | If (e1, e2, e3) ->
      If (strip_label_subst e1, strip_label_subst e2, strip_label_subst e3)
  | _ -> raise Unreachable

let rec strip_label_env (le : Ddeast.lexpr) : Fbenvast.expr =
  let e, _ = le in
  match e with
  | Int i -> Int i
  | Function (Ident x, e) -> Function (Ident x, strip_label_env e)
  | Bool b -> Bool b
  | Appl (e1, e2) -> Appl (strip_label_env e1, strip_label_env e2)
  | Var (Ident x) -> Var (Ident x)
  | Plus (e1, e2) -> Plus (strip_label_env e1, strip_label_env e2)
  | Minus (e1, e2) -> Minus (strip_label_env e1, strip_label_env e2)
  | Equal (e1, e2) -> Equal (strip_label_env e1, strip_label_env e2)
  | And (e1, e2) -> And (strip_label_env e1, strip_label_env e2)
  | Or (e1, e2) -> Or (strip_label_env e1, strip_label_env e2)
  | Not e -> Not (strip_label_env e)
  | If (e1, e2, e3) ->
      If (strip_label_env e1, strip_label_env e2, strip_label_env e3)
  | _ -> raise Unreachable

let dde_parse s =
  s ^ ";;" |> Lexing.from_string
  |> Ddeparser.main Ddelexer.token
  |> strip_label_subst

let dde_eval s =
  Lexing.from_string s
  |> Ddeparser.main Ddelexer.token
  |> Ddeinterp.eval false |> strip_label_subst

let dde_eval_env s =
  Lexing.from_string s
  |> Ddeparser.main Ddelexer.token
  |> Ddeinterp.eval false |> strip_label_env

let fb_eval s =
  Lexing.from_string s |> Fbparser.main Fblexer.token |> Fbinterp.eval

let fbenv_eval s =
  Lexing.from_string s |> Fbenvparser.main Fbenvlexer.token |> Fbenvinterp.eval

let dde_pp e = Format.printf "%a\n" Ddepp.pp_lexpr e
let fb_pp e = Format.printf "%a\n" Fbpp.pp_expr e
let assert_unequal e1 e2 = OUnit2.assert_equal ~cmp:(fun a b -> a <> b) e1 e2
