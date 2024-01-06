open Interp

let toplevel_loop debug simplify =
  (* Print exceptions and associated stack traces *)
  let print_exception ex =
    Format.printf "Exception: %s\n" (Printexc.to_string ex);
    Format.print_flush ();
    Printexc.print_backtrace stdout;
    flush stdout
  in
  let safe_parse () =
    try
      let lexbuf = Lexing.from_channel stdin in
      Some (Parser.main Lexer.token lexbuf)
    with
    | Exit -> exit 0
    | ex ->
        print_exception ex;
        None
  in
  (* Interpret and print. Exceptions are caught and reported. But the toploop is not aborted *)
  let safe_interpret_and_print ast =
    try
      let result, _ = Lib.eval ast ~debug ~simplify in
      Format.printf "==> %a\n" Pp.pp_result_value result
    with ex -> print_exception ex
  in
  while true do
    Format.printf "# ";
    Format.print_flush ();
    let parse_result = safe_parse () in
    match parse_result with
    | None -> ()
    | Some ast ->
        safe_interpret_and_print ast;
        Format.print_flush ()
  done

let run_file filename debug simplify =
  let fin = open_in filename in
  let lexbuf = Lexing.from_channel fin in
  let ast = Parser.main Lexer.token lexbuf in
  let result, _ = Lib.eval ast ~debug ~simplify in
  Format.printf "%a\n" Pp.pp_result_value result;
  Format.print_flush ()

let main () =
  let filename = ref "" in
  let toplevel = ref true in
  let show_exception_stack_trace = ref false in
  let debug = ref false in
  let simplify = ref false in
  Arg.parse
    [
      ( "--show-backtrace",
        Arg.Set show_exception_stack_trace,
        "Enable the display of exception stack traces" );
      ("--debug", Arg.Set debug, "output debug information from evaluation");
      ( "--simplify",
        Arg.Set simplify,
        "eagerly simplify (substitute free variables, perform function \
         application, etc.)result" );
    ]
    (function
      | fname ->
          filename := fname;
          toplevel := false)
    "Interpreter REPL.";

  Printexc.record_backtrace !show_exception_stack_trace;

  if !toplevel then toplevel_loop !debug !simplify
  else run_file !filename !debug !simplify

let () = main ()
