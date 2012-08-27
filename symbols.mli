open Big_int

type version

type comparison = | EQ | LT | LE
                  | NE | GE | GT
 
type ttype =
   (* Unknown_type means the compiler hasn't decided yet,
      but the type will be known by the time type checking
      is complete. *)
   | Unknown_type of unknown
   | Unit_type
   | Boolean_type
   | Integer_type

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
   | Var_version of symbol * version
   | Negation of expr
   | Comparison of comparison * expr * expr

and symbol = {
   sym_id               : int; (* unique identifier *)
   sym_name             : string;
   sym_parent           : symbol option;
   mutable sym_children : symbol list;
   mutable sym_info     : symbol_info;
   mutable sym_last_version
                        : version;
}

and symbol_info =
   | Unfinished_sym (* symbol_info not yet set *)
   | Package_sym
   | Subprogram_sym of subprogram_info
   | Variable_sym
   | Parameter_sym of ttype

and subprogram_info = {
   mutable sub_parameters : symbol list;
   mutable sub_preconditions : expr list;
}

exception Already_defined of symbol

module Ordered : Map.OrderedType with type t = symbol
module Maps    : Map.S with type key = symbol
module Sets    : Set.S with type elt = symbol

val root_symbol : symbol
val full_name : symbol -> string
val full_name_with_version : symbol -> version -> string
val string_of_type : ttype -> string
val string_of_expr : expr -> string
val describe_symbol : symbol -> string
val find_in : symbol -> string -> symbol option
val new_symbol : symbol -> string -> symbol_info -> symbol
val new_version : symbol -> version
val find : symbol -> string -> symbol option
val find_variable : symbol -> string -> symbol
val dump_symbols : unit -> unit
