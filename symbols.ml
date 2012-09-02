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

and unknown = {
   mutable unk_incoming : ttype list;
   mutable unk_outgoing : ttype list;
}

and expr =
   | Boolean_literal of bool
   | Integer_literal of big_int
   | Var of Lexing.position * symbol
   | Var_v of Lexing.position * symbol_v
   | Negation of expr
   | Comparison of comparison * expr * expr

and symbol = {
   sym_id               : int;
   sym_name             : string;
   sym_parent           : symbol option;
   mutable sym_children : symbol list;
   mutable sym_info     : symbol_info;
   mutable sym_versions : symbol_v list;
}

and symbol_v = {
   ver_symbol           : symbol;
   ver_number           : int;
   mutable ver_type     : ttype option;
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

let root_symbol = {
   sym_id            = 0;
   sym_name          = "Standard";
   sym_parent        = None;
   sym_children      = [];
   sym_info          = Package_sym;
   sym_versions      = [];
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
   | Boolean_literal true -> "True"
   | Boolean_literal false -> "False"
   | Integer_literal i -> string_of_big_int i
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
      | Parameter_sym _ -> "parameter"
   ) ^ " `" ^ full_name sym ^ "'"

let find_in scope name =
   try
      Some (List.find
         (fun sym -> sym.sym_name = name)
         scope.sym_children)
   with Not_found -> None

let new_symbol scope name info =
   begin match find_in scope name with
      | None -> ()
      | Some sym ->
         raise (Already_defined sym)
   end;
   incr last_sym_id;
   let new_sym = {
      sym_id            = !last_sym_id;
      sym_name          = name;
      sym_parent        = Some scope;
      sym_children      = [];
      sym_info          = info;
      sym_versions      = [];
   } in
   scope.sym_children <- new_sym :: scope.sym_children;
   new_sym

let new_version sym =
   let sym_v = {
      ver_symbol = sym;
      ver_number =
         (match sym.sym_versions with
            | [] -> 1
            | x::_ -> x.ver_number + 1);
      ver_type = None;
   } in
   sym.sym_versions <- sym_v :: sym.sym_versions;
   sym_v

let find scope name =
   let rec try_scope scope =
      match find_in scope name with
         | Some sym -> Some sym
         | None ->
            match scope.sym_parent with
               | None -> None
               | Some parent -> try_scope parent
   in try_scope scope

let find_variable scope name =
   match find scope name with
      | Some sym -> sym
      | None -> new_symbol scope name Variable_sym

let dump_symbols () =
   let rec dump_sym sym =
      prerr_endline ("Symbol " ^ full_name sym);
      List.iter dump_sym sym.sym_children
   in dump_sym root_symbol
