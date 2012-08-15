exception Internal_error

let string_of_location loc =
    loc.Lexing.pos_fname ^ ":"
    ^ string_of_int loc.Lexing.pos_lnum ^ ":"
    ^ string_of_int (loc.Lexing.pos_cnum + 1 - loc.Lexing.pos_bol)

let syntax_error loc s =
   prerr_endline (
      string_of_location loc
      ^ ": " ^ s)

let semantic_error = syntax_error

let internal_error loc s =
   syntax_error loc ("Internal error: " ^ s);
   raise Internal_error
