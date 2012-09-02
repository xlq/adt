open Symbols
open Icode

val type_check_blocks : block list
                     -> block                (* entry point *)
                     -> (param_mode * ttype) Symbols.Maps.t (* parameters *)
                     -> unit
