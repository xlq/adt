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

exception Bail_out

type context =
   {
      (* Function that's being translated. *)
      ctx_scope      : symbol;
      (* Block to "jump" to after current block. *)
      ctx_after      : block option;
      (* Last source location (where control flow came from). *)
      ctx_last_loc   : Parse_tree.file_location;
   }

type state =
   {
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

let translate_expr
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
   This is so that statements only get translated once each. *)
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
               {context with ctx_after = Some cont} true_part,
            translate_statement state
               {context with ctx_after = Some cont} false_part)
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

let translate (sub: Parse_tree.subprogram): unit =
   let state =
      {
         st_blocks = [];
      }
   in
   match sub.Parse_tree.sub_name with [name] ->
   let subprogram_sym = new_symbol root_symbol name Subprogram_sym in
   let context =
      {
         ctx_scope      = subprogram_sym;
         ctx_after      = None;
         ctx_last_loc   = sub.Parse_tree.sub_location;
      }
   in
   (* Translate parameters. *)
   let parameters = List.fold_left
      (fun parameters param ->
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
                     Symbols.Maps.add sym t parameters
            with Bail_out -> parameters
         ) Symbols.Maps.empty sub.Parse_tree.sub_parameters
   in
   (* Translate preconditions. *)
   let preconditions =
      List.map
         (translate_expr context)
         sub.Parse_tree.sub_preconditions
   in
   (* Translate subprogram body. *)
   let entry_point =
      translate_block state context
         sub.Parse_tree.sub_body
   in

   entry_point.bl_preconditions <- preconditions;

   calculate_free_names state.st_blocks;
   let f = new_formatter () in
   dump_blocks f state.st_blocks;
   prerr_endline (get_fmt_str f);
   Type_checking.type_check_blocks
      state.st_blocks
      entry_point
      parameters
