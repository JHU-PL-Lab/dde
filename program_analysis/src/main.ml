open Program_analysis

let toplevel_loop =
  let print_exception ex =
    Format.printf "Exception: %s\n" (Printexc.to_string ex);
    Format.print_flush ();
    Printexc.print_backtrace stdout;
    flush stdout
  in
  let safe_parse () =
    try
      let lexbuf = Lexing.from_channel stdin in
      Some (Interpreter.Parser.main Interpreter.Lexer.token lexbuf)
    with
    | Exit -> exit 0
    | ex ->
        print_exception ex;
        None
  in
  let safe_analyze_and_print ast =
    try
      let r = Lib.analyze ast ~debug:false in
      Format.printf "==> %a\n" Utils.pp_res r
    with ex -> print_exception ex
  in
  while true do
    Format.printf "# ";
    Format.print_flush ();
    let parse_result = safe_parse () in
    match parse_result with
    | None -> ()
    | Some ast ->
        safe_analyze_and_print ast;
        Format.print_flush ()
  done

let () = toplevel_loop
