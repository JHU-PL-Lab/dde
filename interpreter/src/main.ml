open Interp

let toplevel_loop typechecking_enabled show_types is_debug_mode should_simplify
    =
  (* Prints exceptions and associated stack traces *)
  let print_exception ex =
    Format.printf "Exception: %s\n" (Printexc.to_string ex);
    Format.print_flush ();
    Printexc.print_backtrace stdout;
    flush stdout
  in
  (* Parse the stdin. Our lexers are set up (manually) to generate an Exit *)
  (* exception when Eof is encountered. We abort the top loop in this case. *)
  (* Other parse errors are caught and reported, but we dont abort the top loop *)
  (* TODO: As noted currently it is the lexers themselves that generate this exception. It *)
  (* feels better to have the parsers do this instead. It wont change anything here. But *)
  (* changes are required in each lexer and parser to produce explicit tokens and do the *)
  (* raise *)
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
      let result = Lib.eval ast ~is_debug_mode ~should_simplify in
      Format.printf "==> %a\n" Pp.pp_result_value result
    with ex -> print_exception ex
  in
  Format.printf "\t(typechecker %s)\n\n"
    (if typechecking_enabled then "enabled" else "disabled");
  Format.print_flush ();
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

let run_file filename is_debug_mode should_simplify =
  let fin = open_in filename in
  let lexbuf = Lexing.from_channel fin in
  let ast = Parser.main Lexer.token lexbuf in
  let result = Lib.eval ast ~is_debug_mode ~should_simplify in
  Format.printf "%a\n" Pp.pp_result_value result;
  Format.print_flush ()

let main () =
  let filename = ref "" in
  let toplevel = ref true in
  let version = ref false in
  let no_typechecking = ref false in
  (* let no_typechecking = ref (not Fbdk.Typechecker.typecheck_default_enabled) in *)
  let no_type_display = ref false in
  let show_exception_stack_trace = ref false in
  let is_debug_mode = ref false in
  let should_simplify = ref false in
  Arg.parse
    [
      ("--typecheck", Arg.Clear no_typechecking, "enable typechecking");
      ("--no-typecheck", Arg.Set no_typechecking, "disable typechecking");
      ("--hide-types", Arg.Set no_type_display, "disable displaying of types");
      ( "--show-backtrace",
        Arg.Set show_exception_stack_trace,
        "Enable the display of exception stack traces" );
      ( "--debug",
        Arg.Set is_debug_mode,
        "output debug information from evaluation" );
      ( "--simplify",
        Arg.Set should_simplify,
        "eagerly simplify (substitute free variables, perform function \
         application, etc.)result" );
    ]
    (function
      | fname ->
          filename := fname;
          version := false;
          toplevel := false)
    "Usage: Interp [ options ] [ filename ]\noptions:";

  Printexc.record_backtrace !show_exception_stack_trace;

  if !toplevel then
    toplevel_loop (not !no_typechecking) (not !no_type_display) !is_debug_mode
      !should_simplify
  else run_file !filename !is_debug_mode !should_simplify

let () = main ()
