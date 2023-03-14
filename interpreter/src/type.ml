[@@@coverage off]

open Ast

exception TypecheckerNotImplementedException

(*
 * If you would like typechecking to be enabled by your interpreter by default,
 * then change the following value to true.  Whether or not typechecking is
 * enabled by default, you can explicitly enable it or disable it using
 * command-line arguments. 
 *)
let typecheck_default_enabled = false

(*
 * Replace this with your typechecker code.  Your code should not throw the
 * following exception; if you need to raise an exception, create your own
 * exception type here.
 *)
let typecheck e = raise TypecheckerNotImplementedException
