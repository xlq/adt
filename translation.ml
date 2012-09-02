(* This package contains the second compiler pass.
   This pass accomplishes two things:
   1. The symbol table is constructed, and identifiers and names are bound to
      symbols.
   2. The subprograms are broken up into I-code blocks. Each block is a
      function containing no mutation of local variables and containing
      no control flow merges. Variables live when entering the block
      become the block's parameters. Control flow leaves a block through
      a Jump_term, which is essentially a tail call. *)

open Symbols
open Icode
open Formatting
open Big_int
open Misc

(* This is raised when translation cannot proceed due to an error.
   A compiler error is always produced before raising Bail_out,
   so catching it silently and continuing translation is OK. *)
exception Bail_out

type after =
   (* Block to jump to after current block. *)
   | Continue_with of block
   (* Return_with(sub, constr)
      Return from subprogram sub: the postconditions constr
      must be met. *)
   | Return_with of symbol * expr list

type state =
   {
      mutable st_subprograms:
         (symbol * Parse_tree.subprogram) list;
      mutable st_blocks: block list;
   }

(* Get the source file location of a statement. *)
let get_loc_of_statement = function
   | Parse_tree.No_statement(loc) (* -> raise (Failure "get_loc_of_statement") *)
   | Parse_tree.Null_statement(loc)
   | Parse_tree.Assignment(loc,_,_,_)
   | Parse_tree.If_statement(loc,_,_,_,_)
   | Parse_tree.While_loop(loc,_,_,_)
   | Parse_tree.Inspect_type(loc,_,_) -> loc

(* Get the source file location of an expression. *)
let get_loc_of_expression = function
   | Parse_tree.Boolean_literal(loc,_)
   | Parse_tree.Integer_literal(loc,_)
   | Parse_tree.Name(loc,_) -> loc

let rec translate_type
   (scope: symbol)
   (typ: Parse_tree.ttype): ttype
= match typ with
   | Parse_tree.Named_type(loc, ["Boolean"]) ->
      Boolean_type
   | Parse_tree.Named_type(loc, ["Integer"]) ->
      Integer_type
   | Parse_tree.Named_type(loc, name) ->
      Errors.semantic_error loc
         ("Undefined type `" ^ String.concat "." name ^ "'.");
      raise Bail_out

let rec translate_expr
   (scope: symbol)
   (expression: Parse_tree.expr): expr
=
   match expression with
      | Parse_tree.Name(loc, [name]) ->
         let sym = Symbols.find_variable scope name in
         begin match sym.sym_info with
            | Variable_sym -> Var(loc, sym)
            | Parameter_sym(mode, declared_type) -> Var(loc, sym)
            | _ ->
               Errors.semantic_error loc
                  ("Expression expected but "
                   ^ describe_symbol sym ^ " found.");
               raise Bail_out
         end
      | Parse_tree.Boolean_literal(loc, b) -> Boolean_literal(loc, b)
      | Parse_tree.Integer_literal(loc, i) -> Integer_literal(loc, i)
      | Parse_tree.Comparison(loc, op, lhs, rhs) ->
         Comparison(op,
            translate_expr scope lhs,
            translate_expr scope rhs)

let translate_lvalue
   (scope: symbol)
   (expression: Parse_tree.expr): symbol
=
   match expression with
      | Parse_tree.Name(loc, [name]) ->
         let sym = Symbols.find_variable scope name in
         begin match sym.sym_info with
            | Variable_sym -> sym
            | _ ->
               Errors.semantic_error loc
                  ("Name expected but "
                   ^ describe_symbol sym ^ " found.");
               raise Bail_out
         end

(* Find the block for the given source statement.
   This is so that statements only get translated once each.
   XXX: I don't think a statement would get translated twice anyway. *)
let find_block (state: state) (statement: Parse_tree.statement): block option =
   let rec search = function
      | [] -> None
      | bl :: l when bl.bl_statement == statement -> Some bl
      | bl :: l -> search l
   in search state.st_blocks

let make_jump
   (loc: Lexing.position)
   (target: block): iterm
=
   Jump_term {
      jmp_location = loc;
      jmp_target = target;
      jmp_versions = Symbols.Maps.empty;
   }

(* Create a new block by applying the given translation function. Nothing is
   done if the statement has already been translated.  In either case, returns the
   block corresponding to the translated statement. *)
let make_block
   (state: state)
   (statement: Parse_tree.statement)
   (translate: block -> iterm): block
=
   match find_block state statement with
      | Some bl -> bl
      | None ->
         let new_block =
            {
               bl_id             = new_block_id ();
               bl_statement      = statement;
               bl_body           = None;
               bl_in             = Symbols.Maps.empty;
               bl_preconditions  = [];
            }
         in
         state.st_blocks <- new_block :: state.st_blocks;
         new_block.bl_body <- Some (translate new_block);
         new_block

let interpret_as_lvalue = function
   | Var(loc, x) -> Some (Var_v(loc, new_version x))
   | _ -> None

let rec translate_statement
   (state: state)
   (scope: symbol)
   (after: after)
   (statement: Parse_tree.statement): iterm
=
   match statement with
      | Parse_tree.No_statement(loc) | Parse_tree.Null_statement(loc) ->
         begin match after with
            | Return_with(sub, constraints) ->
               Null_term(
                  loc,
                  List.map
                     (fun constr ->
                        (From_postconditions(loc, sub), constr))
                     constraints)
            | Continue_with cont ->
               make_jump loc cont
         end
      | Parse_tree.Assignment(loc, dest, src, cont) ->
         let dest = translate_expr scope dest in
         let dest = match interpret_as_lvalue dest with
            | Some dest -> dest
            | None ->
               Errors.semantic_error loc
                  ("Cannot assign to `" ^ string_of_expr dest ^ "'.");
               raise Bail_out
         in
         let src = translate_expr scope src in
         let cont = translate_statement state scope after cont in
         Assignment_term(loc, dest, src, cont)
      | Parse_tree.If_statement(loc, condition, true_part, false_part, cont) ->
         let cont = translate_block state scope after cont in
         If_term(loc,
            translate_expr scope condition,
            translate_statement state scope (Continue_with cont) true_part,
            translate_statement state scope (Continue_with cont) false_part)
      | Parse_tree.While_loop(loc, condition, body, cont) ->
         (* XXX: If we're at the start of a block, make_block will do nothing! *)
         let condition_block =
            make_block state statement
               (fun loop_start ->
                  If_term(loc,
                     translate_expr scope condition,
                     translate_statement state scope
                        (Continue_with loop_start) body,
                     translate_statement state scope after cont))
         in
         (*condition_block.bl_free <- !annotations;*)
         make_jump loc condition_block
      | Parse_tree.Subprogram_call(loc, [name], (positional_args, named_args), tail) ->
         begin match Symbols.find scope name with
         | None ->
            Errors.semantic_error loc ("`" ^ name ^ "' is undefined.");
            raise Bail_out
         | Some subprogram_sym ->
            begin match subprogram_sym.sym_info with
            | Subprogram_sym(subprogram_info) ->
               let positional_args = List.map
                  (fun arg ->
                     let arg = translate_expr scope arg in
                     (arg, interpret_as_lvalue arg))
                  positional_args
               in
               let named_args = List.map
                  (fun (name, arg) ->
                     let arg = translate_expr scope arg in
                     (name, (arg, interpret_as_lvalue arg)))
                  named_args
               in
               Call_term(
                  {call_location    = loc;
                   call_target      = subprogram_sym;
                   call_arguments   = (positional_args, named_args);
                   call_bound_arguments = [];
                  },
                  translate_statement state scope after tail)
            | _ ->
               Errors.semantic_error loc
                  ("Subprogram expected but "
                     ^ describe_symbol subprogram_sym
                     ^ " found.");
               raise Bail_out
            end
         end
      | Parse_tree.Inspect_type(loc,[x],tail) ->
         let sym = Symbols.find_variable scope x in
         begin match sym.sym_info with
            | Variable_sym | Parameter_sym(_) -> 
               Inspect_type_term(loc, sym,
                  translate_statement state scope after tail)
            | _ ->
               (* ignore it *)
               translate_statement state scope after tail
         end
      | Parse_tree.Static_assert(loc,expr,tail) ->
         Static_assert_term(loc,
            translate_expr scope expr,
            translate_statement state scope after tail)

and translate_block
   (state: state)
   (scope: symbol)
   (after: after)
   (statement: Parse_tree.statement):
   block
=
   make_block state statement
      (fun _ -> translate_statement state scope after statement)

(* Make a sym -> type map of a subprogram's parameters. *)
let parameters_of_subprogram sym =
   match sym.sym_info with
   | Subprogram_sym(subprogram_info) ->
      List.fold_left (fun result param ->
         match param.sym_info with
            | Parameter_sym(mode, t) ->
               Symbols.Maps.add param (mode, t) result
            | _ ->
               result
         ) Symbols.Maps.empty subprogram_info.sub_parameters

let translate_subprogram_prototype state scope sub =
   match sub.Parse_tree.sub_name with [name] ->
   let subprogram_info = {
      sub_parameters = [];
      sub_preconditions = [];
      sub_postconditions = [];
   } in
   let subprogram_sym =
      try
         new_symbol scope name
            (Subprogram_sym subprogram_info)
      with Already_defined sym ->
         Errors.semantic_error sub.Parse_tree.sub_location
            ("`" ^ name ^ "' already defined as "
               ^ describe_symbol sym ^ ".");
         raise Bail_out
   in
   let scope = subprogram_sym in
   (* Translate parameters. *)
   subprogram_info.sub_parameters <-
      List.fold_right
         (fun param parameters ->
            try
               match Symbols.find_in scope param.Parse_tree.param_name with
                     | Some _ ->
                        Errors.semantic_error sub.Parse_tree.sub_location
                           ("Parameter `" ^ param.Parse_tree.param_name
                              ^ "' defined twice.");
                        raise Bail_out
                     | None ->
                        let sym = new_symbol
                           subprogram_sym
                           param.Parse_tree.param_name
                           Unfinished_sym
                        in
                        let t = translate_type
                           scope param.Parse_tree.param_type
                        in
                        sym.sym_info <- Parameter_sym(param.Parse_tree.param_mode, t);
                        sym :: parameters
               with Bail_out -> parameters
            ) sub.Parse_tree.sub_parameters [];
   (* Translate constraints. *)
   let (pre, post) =
      List.fold_left (fun (pre, post) constr ->
         let e = translate_expr scope constr.Parse_tree.constr_expr in
         match constr.Parse_tree.constr_mode with
            | Const_parameter | In_parameter -> (e::pre, post)
            | Out_parameter -> (pre, e::post)
            | In_out_parameter -> (e::pre, e::post)
      ) ([], []) sub.Parse_tree.sub_constraints
   in
   subprogram_info.sub_preconditions <- pre;
   subprogram_info.sub_postconditions <- post;
   (* Translate the body later. *)
   state.st_subprograms <-
      (subprogram_sym, sub) :: state.st_subprograms

let translate_subprogram_body compiler state subprogram_sym sub =
   let subprogram_info = match subprogram_sym.sym_info with
      | Subprogram_sym(info) -> info
   in
   let parameters = parameters_of_subprogram subprogram_sym in
   let scope = subprogram_sym in
   assert (match state.st_blocks with [] -> true | _ -> false);
   let entry_point =
      translate_block state scope
         (Return_with(subprogram_sym, subprogram_info.sub_postconditions))
         sub.Parse_tree.sub_body
   in
   entry_point.bl_preconditions <- List.map
      (fun precondition ->
         (From_preconditions(
            Symbols.loc_of_expression precondition,
            subprogram_sym),
          precondition))
      subprogram_info.sub_preconditions;
   calculate_free_names state.st_blocks;
   Type_checking.type_check_blocks
      state.st_blocks
      entry_point
      parameters;
   Backend_c.translate compiler subprogram_sym entry_point state.st_blocks;
   state.st_blocks <- []

let translate_declarations state scope declarations =
   List.iter (fun declaration ->
      try
         match declaration with
            | Parse_tree.Subprogram(sub) ->
               translate_subprogram_prototype state scope sub
      with Bail_out -> ()
   ) declarations

let finish_translation compiler state =
   let subs = state.st_subprograms in
   state.st_subprograms <- [];
   List.iter (fun (sym, sub) ->
      Backend_c.declare compiler sym) subs;
   List.iter (fun (sym, sub) ->
      try translate_subprogram_body compiler state sym sub
      with Bail_out -> ()) subs

let translate_package compiler state pkg =
   match pkg.Parse_tree.pkg_name with [name] ->
   let package_sym = new_symbol root_symbol name Package_sym in
   translate_declarations state package_sym
      pkg.Parse_tree.pkg_declarations;
   finish_translation compiler state

let translate compiler translation_unit =
   let state = {
      st_subprograms = [];
      st_blocks = [];
   } in
   match translation_unit with
      | Parse_tree.Subprogram_unit sub ->
         translate_subprogram_prototype state root_symbol sub;
         finish_translation compiler state
      | Parse_tree.Package_unit pkg ->
         translate_package compiler state pkg
