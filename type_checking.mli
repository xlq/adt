open Symbols
open Icode

val type_check_blocks : block list
                     -> block                (* entry point *)
                     -> ttype Symbols.Maps.t (* parameters *)
                     -> unit
