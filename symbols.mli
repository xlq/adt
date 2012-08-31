open Big_int

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
   | Var_v of symbol_v
   | Negation of expr
   | Comparison of comparison * expr * expr

(* A symbol. Each symbol has one symbol object representing it - symbol objects
   can and should be compared physically (i.e. == not =). *)
and symbol = {
   sym_id               : int; (* unique identifier *)
   sym_name             : string;
   sym_parent           : symbol option;
   mutable sym_children : symbol list;
   mutable sym_info     : symbol_info;
   mutable sym_versions : symbol_v list;
}

(* A symbol_v is a version of a symbol. In constraints, etc., each symbol_v is
   a separate variable, even though many symbol_v objects represent the same
   symbol in the source programme (see: static single assignment form).
   Objects of symbol_v can and should be compared physically: there is one
   object for each symbol and version. *)
and symbol_v = {
   ver_symbol           : symbol;
   ver_number           : int; (* for dumping and ordering *)
   mutable ver_type     : ttype;
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

module Maps    : Map.S with type key = symbol
module Sets    : Set.S with type elt = symbol
module Maps_v  : Map.S with type key = symbol_v

val root_symbol : symbol
val dotted_name : symbol -> string list
val full_name : symbol -> string
val full_name_v : symbol_v -> string
val string_of_type : ttype -> string
val string_of_expr : expr -> string
val describe_symbol : symbol -> string
val find_in : symbol -> string -> symbol option
val new_symbol : symbol -> string -> symbol_info -> symbol
val new_version : symbol -> ttype -> symbol_v
val find : symbol -> string -> symbol option
val find_variable : symbol -> string -> symbol
val dump_symbols : unit -> unit
