open Big_int

type comparison = | EQ | LT | LE
                  | NE | GE | GT

and param_mode =
   | Const_parameter
   | In_parameter
   | In_out_parameter
   | Out_parameter

type ttype =
   (* Unknown_type means the compiler hasn't decided yet,
      but the type will be known by the time type checking
      is complete. *)
   | Unknown_type of unknown
   | Unit_type
   | Boolean_type
   | Integer_type
   | Uninitialised of ttype

and unknown = {
   (* Incoming candidate types. These are types from
      the contexts that Jump_terms are typed under. *)
   mutable unk_incoming : ttype list;
   (* Outgoing candidate types. These are the types
      that this type is expected to have (or expected
      to be coerced into). *)
   mutable unk_outgoing : ttype list;
   (* Multiple references to this unknown may exist,
      so this field is set when the type is decided,
      before the Unknown_type is removed. *)
   mutable unk_decided : ttype option;
   (* Used during resolution. *)
   mutable unk_visiting : bool;
}

and expr =
   | Boolean_literal of Lexing.position * bool
   | Integer_literal of Lexing.position * big_int
   | Var of Lexing.position * symbol
   | Var_v of Lexing.position * symbol_v
   | Negation of expr
   | Comparison of comparison * expr * expr

(* A symbol. Each symbol has one symbol object representing it - symbol objects
   can and should be compared physically (i.e. == not =). *)
and symbol = {
   sym_id               : int; (* unique identifier *)
   sym_name             : string;
   sym_declared         : Lexing.position option;
   sym_parent           : symbol option;
   mutable sym_children : symbol list;
   mutable sym_info     : symbol_info;
   mutable sym_last_version
                        : int;
}

(* A symbol_v is a version of a symbol. In constraints, etc., each symbol_v is
   a separate variable, even though many symbol_v objects represent the same
   symbol in the source programme (a bit like static single assignment form).
   Objects of symbol_v can and should be compared physically: there is one
   object for each symbol and version. *)
and symbol_v = {
   ver_symbol           : symbol;
   ver_number           : int; (* for dumping and ordering *)
   mutable ver_type     : ttype;
   (* Used in calculate_versions. *)
   mutable ver_next     : symbol_v option;
}

and symbol_info =
   | Unfinished_sym (* symbol_info not yet set *)
   | Package_sym
   | Subprogram_sym of subprogram_info
   | Variable_sym
   | Parameter_sym of param_mode * ttype

and subprogram_info = {
   mutable sub_parameters : symbol list;
   mutable sub_preconditions : expr list;
   mutable sub_postconditions: expr list;
}

exception Already_defined of symbol

module Maps    : Map.S with type key = symbol
module Sets    : Set.S with type elt = symbol

val loc_of_expression : expr -> Lexing.position
val root_symbol : symbol
val dotted_name : symbol -> string list
val full_name : symbol -> string
val full_name_v : symbol_v -> string
val string_of_type : ttype -> string
val string_of_expr : expr -> string
val string_of_lvalue : expr -> string
val describe_symbol : symbol -> string
val find_in : symbol -> string -> symbol list
val new_symbol : symbol (* scope *)
              -> string (* name *)
              -> Lexing.position option (* declaration position *)
              -> symbol_info
              -> symbol
(* Same as above, but allows creating symbols of the
   same name in the same scope. *)
val new_overloaded_symbol : symbol
                         -> string
                         -> Lexing.position option
                         -> symbol_info
                         -> symbol
val new_version : symbol -> symbol_v
val dump_symbols : unit -> unit

(* Return a list of all the free variables in an expression. *)
val free_variables : expr -> symbol_v list

(* Change all Var to Var_v in an expression. *)
val bind_versions : (symbol -> symbol_v) -> expr -> expr
