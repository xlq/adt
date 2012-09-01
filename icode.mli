(* Intermediate representation.
   A source subprogram is translated into a set of blocks.
   Each block is essentially a function whose parameters
   are variables of the source subprogram that are live
   when the block is entered.
   The intermediate representation contains no control flow
   merges: loops are converted to recursion. This makes
   typing simpler.
   The intermediate representation is in static single assignment form. *)

open Symbols
open Formatting
open Symbols

type loc = Parse_tree.loc

type iterm =
   | Null_term of loc
   | Assignment_term of loc * symbol_v   (* destination *)
                            * expr       (* source *)
                            * iterm      (* continuation *)
   | If_term of loc * expr  (* condition *)
                    * iterm (* true part *)
                    * iterm (* false part *)
   | Jump_term of jump_info
   | Call_term of call_info * iterm
   | Inspect_type_term of loc * symbol * iterm
   | Static_assert_term of loc * expr * iterm

and jump_info =
   {
      (* Source file location. *)
      jmp_location      : loc;
      (* Target of jump. *)
      jmp_target        : block;
      (* Variables bound in this jump.
         Used during liveness analysis. *)
      mutable jmp_bound : Symbols.Sets.t;
   }

and call_info =
   {
      call_location   : loc;
      call_target     : symbol;
      call_arguments  : expr list * (string * expr) list;
      (* call_bound_arguments is set once the target subprogram has been
         chosen. The list is in the same order as the target's parameters. *)
      mutable call_bound_arguments
                      : expr list;
   }

and block =
   {
      (* Unique identifier for dumping. *)
      bl_id                   : int;
      (* The source statement that was translated
         to produce this block. *)
      bl_statement            : Parse_tree.statement;
      (* The result of the translation. *)
      mutable bl_body         : iterm option;
      (* Set of free varibles in the body, with types.
         Analogous to the variables that are
         live when entering the block. *)
      mutable bl_free         : Symbols.Sets.t;
      mutable bl_preconditions: expr list;
      (* XXX: bl_free_types and bl_free are redundant! *)
      mutable bl_in           : symbol_v Symbols.Maps.t;
   }

val new_block_id: unit -> int
val dump_blocks: formatter -> block list -> unit

(* Calculate bl_free. This is essentially liveness analysis. *)
val calculate_free_names: block list -> unit
