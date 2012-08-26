open Big_int
open Misc

type version = int

type comparison = | EQ | LT | LE
                  | NE | GE | GT

type ttype =
   | Unknown_type of unknown
   | Unit_type
   | Boolean_type
   | Integer_type

and unknown = {
   mutable unk_incoming : ttype list;
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
   sym_id               : int;
   sym_name             : string;
   sym_parent           : symbol option;
   mutable sym_children : symbol list;
   mutable sym_info     : symbol_info;
   mutable sym_last_version
                        : version;
}

and symbol_info =
   | Unfinished_sym
   | Package_sym
   | Subprogram_sym of subprogram_info
   | Variable_sym
   | Parameter_sym of ttype

and subprogram_info = {
   mutable sub_preconditions : expr list;
}

let last_sym_id = ref 0

module Ordered = struct
   type t = symbol
   let compare a b = compare a.sym_id b.sym_id
end

module Maps = Map.Make(Ordered)
module Sets = Set.Make(Ordered)

let root_symbol = {
   sym_id            = 0;
   sym_name          = "Standard";
   sym_parent        = None;
   sym_children      = [];
   sym_info          = Package_sym;
   sym_last_version  = 0;
}

let rec full_name sym =
   (match sym.sym_parent with
      | None -> ""
      | Some parent when parent == root_symbol -> ""
      | Some parent ->
         full_name parent ^ ".")
   ^ sym.sym_name

let full_name_with_version sym version =
   full_name sym ^ "#" ^ string_of_int version

let string_of_op = function
   | EQ -> "="
   | NE -> "<>"
   | LT -> "<"
   | GT -> ">"
   | LE -> "<="
   | GE -> ">="

let rec string_of_expr = function
   | Boolean_literal true -> "True"
   | Boolean_literal false -> "False"
   | Integer_literal i -> string_of_big_int i
   | Var sym -> full_name sym
   | Var_version(sym,version) -> full_name_with_version sym version
   | Negation(m) -> "not (" ^ string_of_expr m ^ ")"
   | Comparison(op,m,n) ->
      string_of_expr m ^ " "
         ^ string_of_op op ^ " "
         ^ string_of_expr n

let rec string_of_type = function
   | Unknown_type _ ->
      "<unknown>"
   | Unit_type -> "Unit"
   | Boolean_type -> "Boolean"
   | Integer_type -> "Integer"

let describe_symbol sym =
   (match sym.sym_info with
      | Package_sym     -> "package"
      | Subprogram_sym _-> "subprogram"
      | Variable_sym    -> "variable"
      | Parameter_sym _ -> "parameter"
   ) ^ " `" ^ full_name sym ^ "'"

let find_in scope name =
   try
      Some (List.find
         (fun sym -> sym.sym_name = name)
         scope.sym_children)
   with Not_found -> None

let new_symbol scope name info =
   assert (match find_in scope name with
      | None -> true
      | Some _ -> false);
   incr last_sym_id;
   let new_sym = {
      sym_id            = !last_sym_id;
      sym_name          = name;
      sym_parent        = Some scope;
      sym_children      = [];
      sym_info          = info;
      sym_last_version  = 0;
   } in
   scope.sym_children <- new_sym :: scope.sym_children;
   new_sym

let new_version sym =
   sym.sym_last_version <- sym.sym_last_version + 1;
   sym.sym_last_version

let find = find_in

let find_variable scope name =
   match find scope name with
      | Some sym -> sym
      | None -> new_symbol scope name Variable_sym

let dump_symbols () =
   let rec dump_sym sym =
      prerr_endline ("Symbol " ^ full_name sym);
      List.iter dump_sym sym.sym_children
   in dump_sym root_symbol
