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

type context =
   {
      (* Entity that's being translated. *)
      ctx_scope      : symbol;
      (* Block to "jump" to after current block. *)
      ctx_after      : block option;
      (* Last source location (where control flow came from). *)
      ctx_last_loc   : Parse_tree.file_location;
   }

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
   (context: context)
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
   (context: context)
   (expression: Parse_tree.expr): expr
=
   match expression with
      | Parse_tree.Name(loc, [name]) ->
         let sym = Symbols.find_variable context.ctx_scope name in
         begin match sym.sym_info with
            | Variable_sym -> Var(sym)
            | Parameter_sym(declared_type) -> Var(sym)
            | _ ->
               Errors.semantic_error loc
                  ("Expression expected but "
                   ^ describe_symbol sym ^ " found.");
               raise Bail_out
         end
      | Parse_tree.Boolean_literal(loc, b) -> Boolean_literal(b)
      | Parse_tree.Integer_literal(loc, i) -> Integer_literal(i)
      | Parse_tree.Comparison(loc, op, lhs, rhs) ->
         Comparison(op,
            translate_expr context lhs,
            translate_expr context rhs)

let translate_lvalue
   (context: context)
   (expression: Parse_tree.expr): symbol
=
   match expression with
      | Parse_tree.Name(loc, [name]) ->
         let sym = Symbols.find_variable context.ctx_scope name in
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
   (loc: Parse_tree.file_location)
   (target: block): iterm
=
   Jump_term {
      jmp_location = loc;
      jmp_target = target;
      jmp_bound = Symbols.Sets.empty;
   }

(* Create a new block by applying the given translation function. Nothing is
   done if the statement has already been translated.  In either case, returns the
   block corresponding to the translated statement. *)
let make_block
   (state: state)
   (context: context)
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
               bl_free           = Symbols.Sets.empty;
               bl_preconditions  = [];
               bl_in             = Symbols.Maps.empty;
            }
         in
         state.st_blocks <- new_block :: state.st_blocks;
         new_block.bl_body <- Some (translate new_block);
         new_block

let rec translate_statement
   (state: state)
   (context: context)
   (statement: Parse_tree.statement): iterm
=
   match statement with
      | Parse_tree.No_statement(loc) | Parse_tree.Null_statement(loc) ->
         begin match context.ctx_after with
            | None ->
               Null_term(loc)
            | Some cont ->
               make_jump context.ctx_last_loc cont
         end
      | Parse_tree.Assignment(loc, dest, src, cont) ->
         let dest' = translate_lvalue context dest in
         let src' = translate_expr context src in
         let cont' =
            translate_statement state
               {context with ctx_last_loc = loc}
               cont
         in
         Assignment_term(loc, dest', src', cont')
      | Parse_tree.If_statement(loc, condition, true_part, false_part, cont) ->
         let cont = translate_block state
            {context with ctx_last_loc = loc}
            cont
         in
         If_term(loc,
            translate_expr context condition,
            translate_statement state
               {context with ctx_after = Some cont;
                             ctx_last_loc = loc} true_part,
            translate_statement state
               {context with ctx_after = Some cont;
                             ctx_last_loc = loc} false_part)
      | Parse_tree.While_loop(loc, condition, body, cont) ->
         (* XXX: If we're at the start of a block, make_block will do nothing! *)
         let condition_block =
            make_block state context statement
               (fun loop_start ->
                  If_term(loc,
                     translate_expr context condition,
                     translate_statement state
                        {context with
                           ctx_last_loc = get_loc_of_expression condition;
                           ctx_after = Some loop_start}
                        body,
                     translate_statement state
                        {context with
                           ctx_last_loc = get_loc_of_expression condition}
                        cont))
         in
         (*condition_block.bl_free <- !annotations;*)
         make_jump loc condition_block
      | Parse_tree.Subprogram_call(loc, [name], (positional_args, named_args), tail) ->
         begin match Symbols.find context.ctx_scope name with
         | None ->
            Errors.semantic_error loc ("`" ^ name ^ "' is undefined.");
            raise Bail_out
         | Some subprogram_sym ->
            begin match subprogram_sym.sym_info with
            | Subprogram_sym(subprogram_info) ->
               let positional_args = List.map
                  (translate_expr context)
                  positional_args
               in
               let named_args = List.map
                  (fun (name, arg) -> (name, translate_expr context arg))
                  named_args
               in
               Call_term(
                  {call_location    = loc;
                   call_target      = subprogram_sym;
                   call_arguments   = (positional_args, named_args)},
                  translate_statement state context tail)
            | _ ->
               Errors.semantic_error loc
                  ("Subprogram expected but "
                     ^ describe_symbol subprogram_sym
                     ^ " found.");
               raise Bail_out
            end
         end
      | Parse_tree.Inspect_type(loc,[x],tail) ->
         let sym = Symbols.find_variable context.ctx_scope x in
         begin match sym.sym_info with
            | Variable_sym | Parameter_sym(_) -> 
               Inspect_type_term(loc, sym,
                  translate_statement state context tail)
            | _ ->
               (* ignore it *)
               translate_statement state context tail
         end
      | Parse_tree.Static_assert(loc,expr,tail) ->
         Static_assert_term(loc,
            translate_expr context expr,
            translate_statement state context tail)

and translate_block
   (state: state)
   (context: context)
   (statement: Parse_tree.statement):
   block
=
   make_block state context statement
      (fun _ -> translate_statement state context statement)

(* Make a sym -> type map of a subprogram's parameters. *)
let parameters_of_subprogram sym =
   match sym.sym_info with
   | Subprogram_sym(subprogram_info) ->
      List.fold_left (fun result param ->
         match param.sym_info with
            | Parameter_sym(t) ->
               Symbols.Maps.add param t result
            | _ ->
               result
         ) Symbols.Maps.empty subprogram_info.sub_parameters

let translate_subprogram_prototype state context sub =
   match sub.Parse_tree.sub_name with [name] ->
   let subprogram_info = {
      sub_parameters = [];
      sub_preconditions = [];
   } in
   let subprogram_sym = new_symbol context.ctx_scope name
      (Subprogram_sym subprogram_info)
   in
   let context = {context with
      ctx_scope = subprogram_sym;
      ctx_after = None;
      ctx_last_loc = sub.Parse_tree.sub_location;
   } in
   (* Translate parameters. *)
   subprogram_info.sub_parameters <-
      List.fold_right
         (fun param parameters ->
            try
               match Symbols.find_in
                  context.ctx_scope
                  param.Parse_tree.param_name
               with
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
                           context 
                           param.Parse_tree.param_type
                        in
                        sym.sym_info <- Parameter_sym(t);
                        sym :: parameters
               with Bail_out -> parameters
            ) sub.Parse_tree.sub_parameters [];
   (* Translate preconditions. *)
   subprogram_info.sub_preconditions <-
      List.map
         (translate_expr context)
         sub.Parse_tree.sub_preconditions;
   (* Translate the body later. *)
   state.st_subprograms <-
      (subprogram_sym, sub) :: state.st_subprograms

let translate_subprogram_body state subprogram_sym sub =
   let subprogram_info = match subprogram_sym.sym_info with
      | Subprogram_sym(info) -> info
   in
   let parameters = parameters_of_subprogram subprogram_sym in
   let context = {
      ctx_scope = subprogram_sym;
      ctx_after = None;
      ctx_last_loc = sub.Parse_tree.sub_location;
   } in
   assert (match state.st_blocks with [] -> true | _ -> false);
   let entry_point =
      translate_block state context
         sub.Parse_tree.sub_body
   in
   entry_point.bl_preconditions <- subprogram_info.sub_preconditions;
   calculate_free_names state.st_blocks;
   Type_checking.type_check_blocks
      state.st_blocks
      entry_point
      parameters;
   state.st_blocks <- []

let translate_declarations state context declarations =
   List.iter (fun declaration ->
      try
         match declaration with
            | Parse_tree.Subprogram(sub) ->
               translate_subprogram_prototype state context sub
      with Bail_out -> ()
   ) declarations

let finish_translation state =
   let subs = state.st_subprograms in
   state.st_subprograms <- [];
   List.iter (fun (sym, sub) ->
      try translate_subprogram_body state sym sub
      with Bail_out -> ()) subs

let translate_package state pkg =
   match pkg.Parse_tree.pkg_name with [name] ->
   let package_sym = new_symbol root_symbol name Package_sym in
   let context =
      {
         ctx_scope      = package_sym;
         ctx_after      = None;
         ctx_last_loc   = pkg.Parse_tree.pkg_location;
      }
   in
   translate_declarations state context
      pkg.Parse_tree.pkg_declarations;
   finish_translation state

let translate translation_unit =
   let state = {
      st_subprograms = [];
      st_blocks = [];
   } in
   match translation_unit with
      | Parse_tree.Subprogram_unit sub ->
         let context = {
            ctx_scope      = root_symbol;
            ctx_after      = None;
            ctx_last_loc   = sub.Parse_tree.sub_location
         } in
         translate_subprogram_prototype state context sub;
         finish_translation state
      | Parse_tree.Package_unit pkg ->
         translate_package state pkg
