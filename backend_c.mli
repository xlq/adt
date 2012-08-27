val translate : Options.compiler_options
             -> Symbols.symbol      (* subprogram symbol *)
             -> Icode.block         (* entry point *)
             -> Icode.block list    (* all blocks of subprogram (including entry point) *)
             -> unit
