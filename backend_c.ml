open Symbols
open Options
open Icode
open Misc
open Formatting
open Big_int

let c_name_of_symbol sym =
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
         output_string f "#include \"stdbool.h\"\n";
         options.co_output_file <- Some f

let rec translate_expr = function
   | Boolean_literal(true) -> "true"
   | Boolean_literal(false) -> "false"
   | Integer_literal(i) -> string_of_big_int i
   | Var(x) -> c_name_of_symbol x
   | Negation(e) -> "!(" ^ translate_expr e ^ ")"
   | Comparison(op, lhs, rhs) ->
      "(" ^ translate_expr lhs ^ ") "
         ^ (match op with
            | EQ -> "=="
            | NE -> "!="
            | LT -> "<"
            | LE -> "<="
            | GT -> ">"
            | GE -> ">=")
         ^ " (" ^ translate_expr rhs ^ ")"

let rec translate_icode f = function
   | Null_term _ -> ()
   | Assignment_term(loc, dest, src, tail) ->
      puts f (c_name_of_symbol dest.ver_symbol
         ^ " = " ^ translate_expr src ^ ";");
      break f;
      translate_icode f tail
   | If_term(loc, cond, true_part, false_part) ->
      puts f ("if (" ^ translate_expr cond ^ "){");
      break f; indent f;
      translate_icode f true_part;
      undent f; puts f "} else {"; break f; indent f;
      translate_icode f false_part;
      undent f; puts f "}"; break f
   | Jump_term(jmp) ->
      puts f ("goto block" ^ string_of_int jmp.jmp_target.bl_id ^ ";");
      break f
   (* | Call_term TODO *)
   | Inspect_type_term(_,_,tail) -> translate_icode f tail
   | Static_assert_term(_,_,tail) -> translate_icode f tail

let translate_block f block =
   puts f ("block" ^ string_of_int block.bl_id ^ ": ;");
   break f;
   indent f;
   translate_icode f (unsome block.bl_body);
   undent f

let translate
   (options: compiler_options)
   (subprogram_sym: symbol)
   (entry_point: block)
   (blocks: block list)
=
   match subprogram_sym.sym_info with Subprogram_sym(sub) ->
   start_output options;
   let f = new_formatter () in
   puts f ("void "
      ^ c_name_of_symbol subprogram_sym
      ^ "("
      ^ String.concat ", "
         (List.map
            (fun param ->
               match param.sym_info with Parameter_sym(t) ->
                  c_name_of_type t ^ " " ^ param.sym_name)
            sub.sub_parameters)
      ^ ")");
   break f;
   puts f "{";
   break f; indent f;
   translate_block f entry_point;
   List.iter (fun block ->
      if block != entry_point then
         translate_block f block
   ) blocks;
   undent f;
   puts f "}";
   break f;
   output_string
      (unsome options.co_output_file)
      (get_fmt_str f)
