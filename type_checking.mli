open Symbols
open Icode

val type_check_subprogram_declaration : subprogram_info -> unit

val type_check_blocks : block list
                     -> block (* entry point *)
                     -> unit
