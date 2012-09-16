(* Intermediate representation.
   A source subprogram is translated into a set of blocks.
   Each block is essentially a function whose parameters
   are variables of the source subprogram that are live
   when the block is entered.
   The intermediate representation contains no control flow
   merges: loops are converted to recursion. This makes
   typing simpler. *)

open Symbols
open Formatting
open Symbols

type loc = Parse_tree.loc

(* Reason why a constraint must be solved. *)
type constraint_origin =
   | From_postconditions of Lexing.position (* original location *)
                          * Lexing.position (* Return_term location *)
                          * symbol (* subprogram symbol *)
   | From_preconditions of Lexing.position (* original location *)
                         * Lexing.position (* call location *)
                         * symbol (* subprogram symbol *)
   | From_static_assertion of Lexing.position

type iterm =
   | Assignment_term of loc * expr       (* destination (L-value) *)
                            * expr       (* source *)
                            * iterm      (* continuation *)
   | If_term of loc * expr  (* condition *)
                    * iterm (* true part *)
                    * iterm (* false part *)
   | Return_term of return_info
   | Jump_term of loc * block
   | Call_term of call_info * iterm
   | Inspect_type_term of loc * symbol * iterm
   | Static_assert_term of loc * expr * iterm

and return_info =
   {
      ret_location      : loc;
      (* Subprogram being returned from. *)
      ret_subprogram    : symbol;
      (* Versions of variables to bind to the out parameters
         of the subprogram. This is empty until after
         calculate_free_names. *)
      ret_versions      : symbol_v Symbols.Maps.t;
   }

and call_info =
   {
      call_location   : loc;
      (* Candidate subprograms (more than one here for overloaded
         subprograms). There is always at least one candidate here.
         After resolution, there is *only* one candidate here! *)
      mutable call_candidates : symbol list;
      (* Each argument has a pair of expressions (in, out):
         'in' contains the versions to be passed to the subprogram, while
         'out' contains new versions, for values to be received from the
         subprogram (in the case of Out_parameter or In_out_parameter).
         If the argument was not a valid L-value, out is None. *)
      mutable call_arguments
                      : (expr * expr option) list
                      * (string * (expr * expr option)) list;
      (* call_bound_arguments is set once the target subprogram has been
         chosen. The list is in the same order as the target's parameters. *)
      mutable call_bound_arguments
                      : (expr * expr option) list;
   }

and block =
   {
      (* Unique identifier for dumping. *)
      bl_id                   : int;
      (* The result of the translation. *)
      mutable bl_body         : iterm option;
      (* Set of free varibles in the body, with types.
         Analogous to the variables that are
         live when entering the block. *)
      mutable bl_in           : symbol_v Symbols.Maps.t;
      mutable bl_preconditions: (constraint_origin * expr) list;
   }

val new_block_id: unit -> int
val dump_blocks: formatter -> block list -> unit

(* Get the location in the source that produced a constraint.
   E.g. for a precondition of a call, this returns the location of the call. *)
val loc_of_constraint_origin : constraint_origin -> Lexing.position
val describe_constraint_origin : constraint_origin -> string

(* Calculate bl_in. This is essentially liveness analysis. *)
val calculate_versions: block list -> unit
