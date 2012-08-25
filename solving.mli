open Symbols

val solve : version Symbols.Maps.t (* Avoid eliminating these until the end,
                                      to produce better diagnostics and to
                                      help precondition guessing. *)
         -> expr                   (* Constraints to solve. *)
         -> unit
