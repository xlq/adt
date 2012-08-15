exception Internal_error
val string_of_location : Parse_tree.file_location -> string
val syntax_error : Parse_tree.file_location -> string -> unit
val semantic_error : Parse_tree.file_location -> string -> unit
val internal_error : Parse_tree.file_location -> string -> 'a
