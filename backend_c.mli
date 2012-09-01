val declare : Compiler.compiler
           -> Symbols.symbol
           -> unit
val translate : Compiler.compiler
             -> Symbols.symbol      (* subprogram symbol *)
             -> Icode.block         (* entry point *)
             -> Icode.block list    (* all blocks of subprogram (including entry point) *)
             -> unit
