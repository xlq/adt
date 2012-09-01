exception Internal_error
val string_of_location : Lexing.position -> string
val syntax_error : Lexing.position -> string -> unit
val semantic_error : Lexing.position -> string -> unit
val internal_error : Lexing.position -> string -> 'a
