let string_of_pos pos =
    pos.Lexing.pos_fname ^ ":"
    ^ (string_of_int pos.Lexing.pos_lnum) ^ ":"
    ^ (string_of_int (pos.Lexing.pos_cnum + 1 - pos.Lexing.pos_bol))

let try_parse f lexbuf =
   try
      f Lexer.scan lexbuf
   with Parsing.Parse_error ->
      prerr_endline (string_of_pos (Lexing.lexeme_start_p lexbuf)
         ^ ": Syntax error.");
      raise (Failure "Syntax error.")

let _ =
   let filename = Sys.argv.(1) in
   let f = open_in filename in
   let lexbuf = Lexing.from_channel f in
   lexbuf.Lexing.lex_curr_p <- {
      lexbuf.Lexing.lex_curr_p with
      Lexing.pos_fname = filename
   };

   let sub = try_parse Parser.subprogram lexbuf in
   Translation.translate sub
