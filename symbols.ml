open Big_int
open Misc

type ttype =
   | Unknown_type of ttype option ref
   | Unit_type
   | Boolean_type of discriminant
   | Integer_type of discriminant

and expr =
   | Boolean_literal of bool
   | Integer_literal of big_int
   | Var of symbol
   | Equal of expr * expr
   | For_all of symbol * expr
   | Conjunction of expr list
   | Implication of expr * expr

and discriminant =
   | Unconstrained of symbol option
   | Constrained of expr

and symbol = {
   sym_id               : int;
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

let last_sym_id = ref 0

module Ordered = struct
   type t = symbol
   let compare a b = compare a.sym_id b.sym_id
end

module Maps = Map.Make(Ordered)
module Sets = Set.Make(Ordered)

let root_symbol = {
   sym_id         = 0;
   sym_name       = "Standard";
   sym_parent     = None;
   sym_children   = [];
   sym_info       = Package_sym;
}

let rec full_name sym =
   (match sym.sym_parent with
      | None -> ""
      | Some parent when parent == root_symbol -> ""
      | Some parent ->
         full_name parent ^ ".")
   ^ sym.sym_name

let rec string_of_expr = function
   | Boolean_literal true -> "True"
   | Boolean_literal false -> "False"
   | Integer_literal i -> string_of_big_int i
   | Var sym -> full_name sym
   | Equal(m,n) ->
      string_of_expr m ^ " = " ^ string_of_expr n
   | For_all(a,m) ->
      "{" ^ full_name a ^ "} " ^ string_of_expr m
   | Conjunction p ->
      "(" ^ String.concat ") and ("
         (List.map string_of_expr p) ^ ")"
   | Implication(p,q) ->
      "(if " ^ string_of_expr p
         ^ " then " ^ string_of_expr q ^ ")"

let string_of_disc = function
   | Unconstrained _ -> ""
   | Constrained i -> "(" ^ string_of_expr i ^ ")"

let rec string_of_type = function
   | Unknown_type t ->
      begin match !t with
         | None -> "<unknown>"
         | Some t -> string_of_type t
      end
   | Unit_type -> "Unit"
   | Boolean_type i ->
      "Boolean" ^ string_of_disc i
   | Integer_type i ->
      "Integer" ^ string_of_disc i

let describe_symbol sym =
   (match sym.sym_info with
      | Package_sym     -> "package"
      | Subprogram_sym  -> "subprogram"
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
   } in
   scope.sym_children <- new_sym :: scope.sym_children;
   new_sym

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

let fresh_symbol old_sym =
   incr last_sym_id;
   let new_sym = {
      sym_id        = !last_sym_id;
      sym_name      = old_sym.sym_name ^ "#"
                        ^ string_of_int !last_sym_id;
      sym_parent    = old_sym.sym_parent;
      sym_children  = [];
      sym_info      = old_sym.sym_info}
   in
   let parent = unsome old_sym.sym_parent in
   parent.sym_children <- new_sym :: parent.sym_children;
   new_sym
