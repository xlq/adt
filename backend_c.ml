open Symbols
open Compiler
open Icode
open Misc
open Formatting
open Big_int

type context = {
   tc_vars: symbol_v Symbols.Maps.t;
}

let no_context = {
   tc_vars = Symbols.Maps.empty;
}

let c_name_of_parameter sym =
   sym.sym_name

let c_name_of_variable sym_v =
   sym_v.ver_symbol.sym_name ^ "__" ^ string_of_int sym_v.ver_number

let c_name_of_symbol_v sym_v =
   match sym_v.ver_symbol.sym_info with
      | Variable_sym -> c_name_of_variable sym_v
      | Parameter_sym _ -> c_name_of_parameter sym_v.ver_symbol

let c_name_of_symbol context sym =
   match sym.sym_info with
      | Variable_sym ->
         c_name_of_variable (Symbols.Maps.find sym context.tc_vars)
      | Parameter_sym _ ->
         c_name_of_parameter sym
      | _ ->
         String.concat "__" (dotted_name sym)

let c_name_of_type = function
   | Unit_type -> "void"
   | Boolean_type -> "bool"
   | Integer_type -> "int"

let start_output options =
   match options.co_output_file with
      | Some _ -> ()
      | None ->
         let f = open_out options.co_output_file_name in
         output_string f "#include \"stdbool.h\"\n\n";
         options.co_output_file <- Some f

let paren prec (sprec, s) =
   if prec > sprec then
      "(" ^ s ^ ")"
   else
      s

(* The numbers are precedences to avoid generating excessive parentheses. *)
let rec translate_expr context = function
   | Boolean_literal(true) -> 100, "true"
   | Boolean_literal(false) -> 100, "false"
   | Integer_literal(i) -> 100, string_of_big_int i
   | Var_v(_,x) ->
      begin match x.ver_symbol.sym_info with
         | Parameter_sym((Const_parameter | In_parameter), _)
         | Variable_sym ->
            100, c_name_of_symbol_v x
         | Parameter_sym((In_out_parameter | Out_parameter), _) ->
            90, ("*" ^ c_name_of_symbol_v x)
      end
   | Negation(e) ->
      let e = translate_expr context e in
      90, "!" ^ paren 90 e
   | Comparison(op, lhs, rhs) ->
      let lhs = translate_expr context lhs in
      let rhs = translate_expr context rhs in
      50, paren 50 lhs ^ " "
         ^ (match op with
            | EQ -> "=="
            | NE -> "!="
            | LT -> "<"
            | LE -> "<="
            | GT -> ">"
            | GE -> ">=")
         ^ " " ^ paren 50 rhs

let translate_lvalue context = function
   | Var_v(_,x) ->
      begin match x.ver_symbol.sym_info with
         | Parameter_sym(_, _) ->
            "*" ^ c_name_of_symbol_v x
         | Variable_sym ->
            c_name_of_symbol_v x
      end

let rec translate_icode context f = function
   | Null_term _ -> ()
   | Assignment_term(loc, dest, src, tail) ->
      puts f (translate_lvalue context dest
         ^ " = " ^ snd (translate_expr context src) ^ ";");
      break f;
      translate_icode context f tail
   | If_term(loc, cond, true_part, false_part) ->
      puts f ("if (" ^ snd (translate_expr context cond) ^ "){");
      break f; indent f;
      translate_icode context f true_part;
      undent f; puts f "} else {"; break f; indent f;
      translate_icode context f false_part;
      undent f; puts f "}"; break f
   | Jump_term(jmp) ->
      puts f ("goto block" ^ string_of_int jmp.jmp_target.bl_id ^ ";");
      break f
   | Call_term(call, tail) ->
      puts f (c_name_of_symbol context call.call_target ^ "("
         ^ String.concat ", "
            (List.map (fun arg -> snd (translate_expr context arg)) call.call_bound_arguments)
         ^ ");");
      break f;
      translate_icode context f tail
   | Inspect_type_term(_,_,tail) -> translate_icode context f tail
   | Static_assert_term(_,_,tail) -> translate_icode context f tail

let translate_block context f block =
   puts f ("block" ^ string_of_int block.bl_id ^ ": ;");
   break f;
   indent f;
   translate_icode context f (unsome block.bl_body);
   undent f

let declare_locals f subprogram_sym =
   List.iter (fun sym ->
      match sym.sym_info with
         | Variable_sym ->
            List.iter (fun sym_v ->
               puts f (c_name_of_type (unsome sym_v.ver_type)
                  ^ " " ^ c_name_of_symbol_v sym_v ^ ";");
               break f
            ) sym.sym_versions
         | _ -> ()
   ) subprogram_sym.sym_children

let declare_function f subprogram_sym =
   match subprogram_sym.sym_info with Subprogram_sym(sub) ->
   puts f ("void "
      ^ c_name_of_symbol no_context subprogram_sym
      ^ "("
      ^ String.concat ", "
         (List.map
            (fun param ->
               match param.sym_info with
                  | Parameter_sym((Const_parameter | In_parameter), t) ->
                     c_name_of_type t ^ " " ^ param.sym_name
                  | Parameter_sym((Out_parameter | In_out_parameter), t) ->
                     c_name_of_type t ^ " *" ^ param.sym_name)
            sub.sub_parameters)
      ^ ")")

let declare
   (compiler: compiler)
   (subprogram_sym: symbol)
=
   start_output compiler;
   let f = new_formatter () in
   declare_function f subprogram_sym;
   puts f ";";
   break f;
   break f;
   output_string
      (unsome compiler.co_output_file)
      (get_fmt_str f)

let translate
   (compiler: compiler)
   (subprogram_sym: symbol)
   (entry_point: block)
   (blocks: block list)
=
   start_output compiler;
   let f = new_formatter () in
   declare_function f subprogram_sym;
   break f;
   puts f "{";
   break f; indent f;

   declare_locals f subprogram_sym;
   break f;
   translate_block {tc_vars=Symbols.Maps.map snd entry_point.bl_in} f entry_point;
   List.iter (fun block ->
      if block != entry_point then
         translate_block {tc_vars=Symbols.Maps.map snd block.bl_in} f block
   ) blocks;
   undent f;
   puts f "}";
   break f;
   break f;
   output_string
      (unsome compiler.co_output_file)
      (get_fmt_str f)
