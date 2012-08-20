open Big_int
 
type ttype =
   (* Unknown_type means the compiler hasn't decided yet,
      but the type will be known by the time type checking
      is complete. *)
   | Unknown_type of unknown
   | Unit_type
   | Boolean_type of discriminant
   | Integer_type of discriminant

and unknown = {
   (* Incoming candidate types. These are types from
      the contexts that Jump_terms are typed under. *)
   mutable unk_incoming : ttype list;
   (* Outgoing candidate types. These are the types
      that this type is expected to have (or expected
      to be coerced into). *)
   mutable unk_outgoing : ttype list;
}
   
and expr =
   | Boolean_literal of bool
   | Integer_literal of big_int
   | Var of symbol
   | Equal of expr * expr
   | For_all of symbol * expr
   | Conjunction of expr list
   | Implication of expr * expr

and discriminant =
   (* Symbol represents source of type, and is used
      to create fresh variables. *)
   | Unconstrained of symbol option
   | Constrained of expr

and symbol = {
   sym_id               : int; (* unique identifier *)
   sym_name             : string;
   sym_parent           : symbol option;
   mutable sym_children : symbol list;
   mutable sym_info     : symbol_info;
}

and symbol_info =
   | Unfinished_sym
   | Package_sym
   | Subprogram_sym
   | Variable_sym
   | Parameter_sym of ttype

module Ordered : Map.OrderedType with type t = symbol
module Maps    : Map.S with type key = symbol
module Sets    : Set.S with type elt = symbol

val root_symbol : symbol
val full_name : symbol -> string
val string_of_type : ttype -> string
val string_of_expr : expr -> string
val describe_symbol : symbol -> string
val find_in : symbol -> string -> symbol option
val new_symbol : symbol -> string -> symbol_info -> symbol
val find : symbol -> string -> symbol option
val find_variable : symbol -> string -> symbol
val dump_symbols : unit -> unit
val fresh_symbol : symbol -> symbol
