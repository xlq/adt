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

(* Reason why a variable is live at a particular point. *)
type liveness_origin =
   | Used_variable of Lexing.position
   | From_parameters

type iterm =
   | Null_term of loc
   | Assignment_term of loc * expr       (* destination *)
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
      (* Versions of variables to bind to the free variables of jmp_target
         (i.e. jmp_target.bl_free). This is empty until after
         calculate_free_names. *)
      jmp_versions      : symbol_v Symbols.Maps.t;
   }

and call_info =
   {
      call_location   : loc;
      call_target     : symbol;
      (* Each argument has a pair of expressions (in, out):
         'in' contains the versions to be passed to the subprogram, while
         'out' contains new versions, for values to be received from the
         subprogram (in the case of Out_parameter or In_out_parameter). *)
      call_arguments  : (expr * expr) list * (string * (expr * expr)) list;
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
      mutable bl_in           : (liveness_origin * symbol_v) Symbols.Maps.t;
      mutable bl_preconditions: expr list;
   }

val new_block_id: unit -> int
val dump_blocks: formatter -> block list -> unit

(* Calculate bl_free. This is essentially liveness analysis. *)
val calculate_free_names: block list -> unit
