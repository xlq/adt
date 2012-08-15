open Symbols
open Icode

val type_check_blocks : block list
                     -> block                 (* entry point *)
                     -> context * expr list   (* parameters, preconditions *)
                     -> unit
