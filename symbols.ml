open Big_int
open Misc

type comparison = | EQ | LT | LE
                  | NE | GE | GT

and param_mode =
   | Const_parameter
   | In_parameter
   | In_out_parameter
   | Out_parameter

type ttype =
   | Unknown_type of unknown
   | Unit_type
   | Boolean_type
   | Integer_type
   | Uninitialised of ttype

and unknown = {
   mutable unk_incoming : ttype list;
   mutable unk_outgoing : ttype list;
   mutable unk_decided  : ttype option;
   mutable unk_visiting : bool;
}

and expr =
   | Boolean_literal of Lexing.position * bool
   | Integer_literal of Lexing.position * big_int
   | Var of Lexing.position * symbol
   | Var_v of Lexing.position * symbol_v
   | Negation of expr
   | Comparison of comparison * expr * expr

and symbol = {
   sym_id               : int;
   sym_name             : string;
   sym_declared         : Lexing.position option;
   sym_parent           : symbol option;
   mutable sym_children : symbol list;
   mutable sym_info     : symbol_info;
   mutable sym_last_version
                        : int;
}

and symbol_v = {
   ver_symbol           : symbol;
   ver_number           : int;
   mutable ver_type     : ttype;
   mutable ver_next     : symbol_v option;
}

and symbol_info =
   | Unfinished_sym
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

let last_sym_id = ref 0

module Ordered = struct
   type t = symbol
   let compare a b = compare a.sym_id b.sym_id
end

module Maps = Map.Make(Ordered)
module Sets = Set.Make(Ordered)

let rec loc_of_expression = function
   | Boolean_literal(loc,_) | Integer_literal(loc,_)
   | Var(loc,_) | Var_v(loc,_) -> loc
   | Negation(e) -> loc_of_expression e
   | Comparison(_,lhs,_) -> loc_of_expression lhs

let root_symbol = {
   sym_id            = 0;
   sym_name          = "Standard";
   sym_declared      = None;
   sym_parent        = None;
   sym_children      = [];
   sym_info          = Package_sym;
   sym_last_version  = 0;
}

let dotted_name sym =
   let rec loop result sym =
      if sym == root_symbol then result
      else loop (sym.sym_name :: result) (unsome sym.sym_parent)
   in loop [] sym

let rec full_name sym =
   String.concat "." (dotted_name sym)

let full_name_v sym_v =
   full_name sym_v.ver_symbol ^ "#" ^ string_of_int sym_v.ver_number

let string_of_op = function
   | EQ -> "="
   | NE -> "<>"
   | LT -> "<"
   | GT -> ">"
   | LE -> "<="
   | GE -> ">="

let rec string_of_expr = function
   | Boolean_literal(_,true) -> "True"
   | Boolean_literal(_,false) -> "False"
   | Integer_literal(_,i) -> string_of_big_int i
   | Var(_,sym) -> full_name sym
   | Var_v(_,sym_v) -> full_name_v sym_v
   | Negation(m) -> "not (" ^ string_of_expr m ^ ")"
   | Comparison(op,m,n) ->
      string_of_expr m ^ " "
         ^ string_of_op op ^ " "
         ^ string_of_expr n

let rec string_of_type = function
   | Unknown_type _ -> "<unknown>"
   | Unit_type -> "Unit"
   | Boolean_type -> "Boolean"
   | Integer_type -> "Integer"

let describe_symbol sym =
   (match sym.sym_info with
      | Package_sym     -> "package"
      | Subprogram_sym _-> "subprogram"
      | Variable_sym    -> "variable"
      | Parameter_sym(mode, _) ->
         (match mode with
            | Const_parameter -> ""
            | In_parameter -> "in "
            | Out_parameter -> "out "
            | In_out_parameter -> "in out "
            ) ^ "parameter"
   ) ^ " `" ^ full_name sym ^ "'"

let find_in scope name =
   List.filter
      (fun sym -> sym.sym_name = name)
      scope.sym_children

let new_overloaded_symbol scope name loc info =
   incr last_sym_id;
   let new_sym = {
      sym_id            = !last_sym_id;
      sym_name          = name;
      sym_declared      = loc;
      sym_parent        = Some scope;
      sym_children      = [];
      sym_info          = info;
      sym_last_version  = 0;
   } in
   scope.sym_children <- new_sym :: scope.sym_children;
   new_sym

let new_symbol scope name loc info =
   begin match find_in scope name with
      | [] -> ()
      | sym::_ ->
         raise (Already_defined sym)
   end;
   new_overloaded_symbol scope name loc info

let new_version sym =
   sym.sym_last_version <- sym.sym_last_version + 1;
   {
      ver_symbol = sym;
      ver_number = sym.sym_last_version;
      ver_type = Unknown_type {
         unk_incoming = [];
         unk_outgoing = [];
         unk_decided = None;
         unk_visiting = false
      };
      ver_next = None;
   }

let dump_symbols () =
   let rec dump_sym sym =
      prerr_endline ("Symbol " ^ full_name sym);
      List.iter dump_sym sym.sym_children
   in dump_sym root_symbol
