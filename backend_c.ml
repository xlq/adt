open Symbols
open Compiler
open Icode
open Misc
open Formatting
open Big_int

let rec erase_type t =
   match t with
      | Boolean_type -> Boolean_type
      | Integer_type -> Integer_type
      | Uninitialised(t) -> erase_type t

let collect_types_type types loc x t =
   let t = erase_type t in
   match
      begin try Some (Symbols.Maps.find x !types)
      with Not_found -> None end
   with
      | None -> types := Symbols.Maps.add x t !types
      | Some t2 when same_types t t2 -> ()
      | Some t2 ->
         Errors.semantic_error loc
            (String.capitalize (describe_symbol x)
               ^ " has type `"
               ^ string_of_type t ^ "' here and type `"
               ^ string_of_type t2 ^ "' elsewhere. These types"
               ^ " cannot be stored in the same location.")

let rec collect_types_expr types = function
   | Boolean_literal _ -> ()
   | Integer_literal _ -> ()
   | Var_v(loc, xv) ->
      collect_types_type types loc xv.ver_symbol xv.ver_type
   | Negation(e) -> collect_types_expr types e
   | Comparison(op, lhs, rhs) ->
      collect_types_expr types lhs;
      collect_types_expr types rhs

let rec collect_types_iterm types = function
   | Assignment_term(loc, dest, src, tail) ->
      collect_types_expr types src;
      collect_types_expr types dest;
      collect_types_iterm types tail
   | If_term(loc, condition, true_part, false_part) ->
      collect_types_expr types condition;
      collect_types_iterm types true_part;
      collect_types_iterm types false_part
   | Return_term _ -> ()
   | Jump_term _ -> ()
   | Call_term(call, tail) ->
      List.iter (fun (arg_in, arg_out) ->
         collect_types_expr types arg_in;
         match arg_out with
            | None -> ()
            | Some arg_out ->
               collect_types_expr types arg_out
      ) (fst call.call_arguments);
      List.iter (fun (_, (arg_in, arg_out)) ->
         collect_types_expr types arg_in;
         match arg_out with
            | None -> ()
            | Some arg_out ->
               collect_types_expr types arg_out
      ) (snd call.call_arguments);
      collect_types_iterm types tail

let collect_types_blocks types blocks =
   List.iter (fun block ->
      collect_types_iterm types (unsome block.bl_body)
   ) blocks

let c_name_of_local sym =
   sym.sym_name

let c_name_of_symbol sym =
   match sym.sym_info with
      | Variable_sym | Parameter_sym _ ->
         c_name_of_local sym
      | _ ->
         String.concat "__" (dotted_name sym)

let c_name_of_type = function
   | Boolean_type -> "bool"
   | Integer_type -> "int"

let c_name_of_subprogram ({sym_info = Subprogram_sym(info)} as sym) =
   c_name_of_symbol sym
      ^ (if info.sub_overload_num == 0 then ""
         else "__" ^ string_of_int info.sub_overload_num)

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
let rec translate_expr = function
   | Boolean_literal(_,true) -> 100, "true"
   | Boolean_literal(_,false) -> 100, "false"
   | Integer_literal(_,i) -> 100, string_of_big_int i
   | Var_v(_,x) ->
      begin match x.ver_symbol.sym_info with
         | Parameter_sym((Const_parameter | In_parameter), _)
         | Variable_sym ->
            100, c_name_of_local x.ver_symbol
         | Parameter_sym((In_out_parameter | Out_parameter), _) ->
            90, ("*" ^ c_name_of_local x.ver_symbol)
      end
   | Negation(e) ->
      let e = translate_expr e in
      90, "!" ^ paren 90 e
   | Comparison(op, lhs, rhs) ->
      let lhs = translate_expr lhs in
      let rhs = translate_expr rhs in
      50, paren 50 lhs ^ " "
         ^ (match op with
            | EQ -> "=="
            | NE -> "!="
            | LT -> "<"
            | LE -> "<="
            | GT -> ">"
            | GE -> ">=")
         ^ " " ^ paren 50 rhs

let translate_lvalue = function
   | Var_v(_,x) ->
      begin match x.ver_symbol.sym_info with
         | Parameter_sym(_, _) ->
            "*" ^ c_name_of_local x.ver_symbol
         | Variable_sym ->
            c_name_of_local x.ver_symbol
      end

let rec translate_icode f = function
   | Return_term _ ->
      puts f "return;";
      break f
   | Assignment_term(loc, dest, src, tail) ->
      puts f (translate_lvalue dest
         ^ " = " ^ snd (translate_expr src) ^ ";");
      break f;
      translate_icode f tail
   | If_term(loc, cond, true_part, false_part) ->
      puts f ("if (" ^ snd (translate_expr cond) ^ "){");
      break f; indent f;
      translate_icode f true_part;
      undent f; puts f "} else {"; break f; indent f;
      translate_icode f false_part;
      undent f; puts f "}"; break f
   | Jump_term(loc, target) ->
      puts f ("goto block" ^ string_of_int target.bl_id ^ ";");
      break f
   | Call_term(call, tail) ->
      let [target] = call.call_candidates in
      puts f (c_name_of_subprogram target ^ "("
         ^ String.concat ", "
            (List.map (fun (arg, _) -> snd (translate_expr arg)) call.call_bound_arguments)
         ^ ");");
      break f;
      translate_icode f tail
   | Inspect_type_term(_,_,tail) -> translate_icode f tail
   | Static_assert_term(_,_,tail) -> translate_icode f tail

let translate_block f block =
   puts f ("block" ^ string_of_int block.bl_id ^ ": ;");
   break f;
   indent f;
   translate_icode f (unsome block.bl_body);
   undent f

let declare_locals f types =
   Symbols.Maps.iter (fun x t ->
      match x.sym_info with
         | Variable_sym ->
            puts f (c_name_of_type t
               ^ " " ^ c_name_of_local x ^ ";");
            break f
         | Parameter_sym _ ->
            ()
   ) types

let declare_function f subprogram_sym =
   match subprogram_sym.sym_info with Subprogram_sym(sub) ->
   puts f ("void "
      ^ c_name_of_subprogram subprogram_sym
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

   let types = ref Symbols.Maps.empty in
   collect_types_blocks types blocks;

   declare_locals f !types;
   break f;
   translate_block f entry_point;
   List.iter (fun block ->
      if block != entry_point then
         translate_block f block
   ) blocks;
   undent f;
   puts f "}";
   break f;
   break f;
   output_string
      (unsome compiler.co_output_file)
      (get_fmt_str f)
