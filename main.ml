open Options

let string_of_pos pos =
    pos.Lexing.pos_fname ^ ":"
    ^ (string_of_int pos.Lexing.pos_lnum) ^ ":"
    ^ (string_of_int (pos.Lexing.pos_cnum + 1 - pos.Lexing.pos_bol))

let c_from_source_file_name input_name =
   let prefix =
      try
         String.sub input_name 0
            (String.rindex input_name '.')
      with Not_found ->
         input_name
   in
   prefix ^ ".c"


let try_parse f lexbuf =
   try
      f Lexer.scan lexbuf
   with Parsing.Parse_error ->
      prerr_endline (string_of_pos (Lexing.lexeme_start_p lexbuf)
         ^ ": Syntax error.");
      raise (Failure "Syntax error.")

let _ =
   let input_name = Sys.argv.(1) in
   let f = open_in input_name in
   let lexbuf = Lexing.from_channel f in
   lexbuf.Lexing.lex_curr_p <- {
      lexbuf.Lexing.lex_curr_p with
      Lexing.pos_fname = input_name
   };

   let options = {
      co_output_file_name = c_from_source_file_name input_name;
      co_output_file = None;
   } in

   let translation_unit = try_parse Parser.translation_unit lexbuf in
   Translation.translate options translation_unit
