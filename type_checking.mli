open Symbols
open Icode

val type_check_subprogram_declaration : subprogram_info -> unit

val check_overload : symbol list -> symbol -> unit

val type_check_blocks : block list -> unit
