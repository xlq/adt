open Symbols
open Icode
open Misc
open Big_int

type pass =
   (* Guessing pass - unknown types are guessed. *)
   | Guessing_pass
   (* Checking pass - unknown types are rejected. *)
   | Checking_pass

type context = {
   (* The current pass. *)
   tc_pass     : pass;
   (* The type that's expected of the term or expression being
      typed under this context. *)
   tc_expected : ttype option;
   (* Boolean expressions known true. *)
   tc_facts    : expr list;
}

type state = {
   (* List of unsolved constraints. *)
   mutable ts_unsolved  : (Lexing.position * expr) list;
}

exception Type_error
exception Unresolved_unknown
exception Unsolved_constraint

let assert_unit t =
   assert (match t with
      | Unit_type -> true
      | _ -> false)

let report_liveness_origin sym = function
   | Used_variable loc ->
      Errors.semantic_error loc
         (String.capitalize (describe_symbol sym)
            ^ " is used here.")

(* Substitute a variable with a term, in the given expression. *)
let rec subst x_sym replacement expr =
   let r = subst x_sym replacement in
   match expr with
      | Boolean_literal _ | Integer_literal _ -> expr
      | Var(_,x) when (x_sym == x) ->
         replacement
      | Var _ -> expr
      | Negation(e) -> Negation(r e)
      | Comparison(op, lhs, rhs) -> Comparison(op, r lhs, r rhs)

(* Same as subst but specifies a variable version. *)
let rec substv x replacement expr =
   let r = substv x replacement in
   match expr with
      | Boolean_literal _ | Integer_literal _ -> expr
      | Var_v(_,x') when x == x' -> replacement
      | Var_v _ -> expr
      | Negation(e) -> Negation(r e)
      | Comparison(op, lhs, rhs) -> Comparison(op, r lhs, r rhs)

let negate = function
   | Boolean_literal(b) -> Some(Boolean_literal(not b))
   | Integer_literal _ | Var _ | Var_v _ -> None
   | Comparison(op, lhs, rhs) ->
      Some(Comparison(
         (match op with
            | EQ -> NE | NE -> EQ
            | LT -> GE | GE -> LT
            | LE -> GT | GT -> LE),
         lhs, rhs))

let rec normalise (e: expr) =
   match e with
      | Boolean_literal _ | Integer_literal _
      | Var _ | Var_v _ -> e
      | Negation(e) ->
         begin match negate e with
            | Some e' -> normalise e'
            | None -> Negation(normalise e)
         end
      | Comparison((EQ|NE|LT|LE), _, _) -> e
      | Comparison(GT, lhs, rhs) -> Comparison(LT, rhs, lhs)
      | Comparison(GE, lhs, rhs) -> Comparison(LE, rhs, lhs)

let rec expressions_match m n =
   match m, n with
      | Boolean_literal(b), Boolean_literal(b') -> b = b'
      | Integer_literal(i), Integer_literal(i') -> eq_big_int i i'
      | Var_v(_,x), Var_v(_,x') -> x == x'
      | Negation(x), Negation(x') -> expressions_match x x'
      | Comparison(op, lhs, rhs), Comparison(op', lhs', rhs') ->
         (op = op') && (expressions_match lhs lhs')
                    && (expressions_match rhs rhs')
      | Boolean_literal _, _ | _, Boolean_literal _
      | Integer_literal _, _ | _, Integer_literal _
      | Var_v _, _ | _, Var_v _
      | Negation _, _ | _, Negation _
      | Comparison _, _ | _, Comparison _ ->
         false

(* Eliminate M = N by substituting M -> N. *)
let elim_equals facts e =
   let rec loop facts e = function
      | [] -> (facts, e)
      | (Comparison(EQ, Var_v(_,x), m))::tail
      | (Comparison(EQ, m, Var_v(_,x)))::tail ->
         prerr_endline ("Substituting "
            ^ full_name_v x ^ " |-> "
            ^ string_of_expr m);
         loop
            (List.map (substv x m) facts)
            (substv x m e)
            (List.map (substv x m) tail)
      | m::tail ->
         loop (m::facts) e tail
   in loop [] e facts

let prove
   (state: state)
   (context: context)
   (loc: Lexing.position)
   (to_prove: expr): unit
=
   prerr_endline ("Proving "
      ^ string_of_expr to_prove
      ^ " under assumptions "
      ^ String.concat " and "
         (List.map string_of_expr context.tc_facts));
   let facts = List.map normalise context.tc_facts in
   let e = normalise to_prove in

   let facts, e = elim_equals facts e in

   if List.exists (expressions_match e) facts then
      (* Trivial case: we already know e is true. *)
      ()
   else match e with
      | Comparison((LT|LE), lhs, rhs) ->
         let linear_e = Fm_solver.linearise e in
         let linear_facts =
            List.fold_left (fun linear_facts fact ->
               try
                  Fm_solver.linearise fact @ linear_facts
               with Fm_solver.Non_linear_constraint ->
                  linear_facts
            ) [] facts
         in
         let inequalities = linear_facts @ (List.map Fm_solver.negate linear_e) in
         (* We must now prove that the inequalities are not satisfiable. *)
         try
            Fm_solver.solve inequalities;
            (* Solving succeeded: the inequalities were satisfiable.
               The original constraint was not proved. *)
            state.ts_unsolved <- (loc, to_prove) :: state.ts_unsolved
         with Fm_solver.Contradiction -> ()

let rec coerce context t1 t2: ttype =
   try
      match t1, t2 with
         | Unit_type, Unit_type ->
            Unit_type
         | Boolean_type, Boolean_type
         | Integer_type, Integer_type ->
            t1
         | Unknown_type(unk), t2 ->
            begin match context.tc_pass with
               | Guessing_pass ->
                  prerr_endline "Coercing from Unknown_type.";
                  unk.unk_outgoing <- t2 :: unk.unk_outgoing;
                  t2
               | Checking_pass ->
                  raise Unresolved_unknown
            end
         | t1, Unknown_type(unk) ->
            begin match context.tc_pass with
               | Guessing_pass ->
                  prerr_endline "Coercing to Unknown_type.";
                  unk.unk_incoming <- t1 :: unk.unk_incoming;
                  t1
               | Checking_pass ->
                  raise Unresolved_unknown
            end
   with (Match_failure _) as e ->
      prerr_endline ("Match failure when trying to coerce `"
         ^ string_of_type t1 ^ "' into `" ^ string_of_type t2
         ^ "'.");
      raise e

let got_type
   (context: context)
   (t: ttype): ttype
=
   match context.tc_expected with
      | None -> t
      | Some t2 -> coerce context t t2

let rec type_check_expr
   (context: context)
   (expr: expr): ttype
= match expr with
   | Boolean_literal(b) ->
      got_type context Boolean_type
   | Integer_literal(i) ->
      got_type context Integer_type
   | Var_v(loc,x) ->
      begin match x.ver_type with
         | None ->
            Errors.semantic_error loc
               (String.capitalize (describe_symbol x.ver_symbol)
                  ^ " might not be initialised yet.");
            raise Type_error
         | Some t ->
            got_type context t
      end
   | Comparison(op, lhs, rhs) ->
      let operand_context = {context with tc_expected = None} in
      let lhs_t = type_check_expr operand_context lhs in
      let rhs_t = type_check_expr operand_context rhs in
      ignore (coerce context lhs_t rhs_t);
      got_type context Boolean_type

let assign_to_lvalue
   (context: context)
   (dest: expr)
   (src_type: ttype)
= match dest with
   | Var_v(_, x) -> x.ver_type <- Some src_type

let rec type_check
   (state: state)
   (context: context)
   (iterm: iterm): ttype
= match iterm with
   | Null_term(loc) ->
      got_type context Unit_type
   | Assignment_term(loc, dest, src, tail) ->
      let src_type =
         type_check_expr
            {context with tc_expected = None}
            src
      in
      assign_to_lvalue context dest src_type;
      type_check
         state
         {context with
            tc_facts =
               Comparison(EQ, dest, src)
                  :: context.tc_facts}
         tail
   | If_term(loc, condition, true_part, false_part) ->
      ignore (type_check_expr
         {context with
            tc_expected = Some Boolean_type}
         condition);
      let true_part_type =
         type_check
            state
            {context with
               tc_facts = condition :: context.tc_facts}
            true_part
      in
      let false_part_type =
         type_check
            state
            {context with
               tc_facts = Negation(condition) :: context.tc_facts}
         false_part
      in
      assert_unit true_part_type;
      assert_unit false_part_type;
      begin match context.tc_expected with
         | None -> ()
         | Some t -> assert_unit t
      end;
      Unit_type
   | Jump_term(jmp) ->
      let preconditions = ref jmp.jmp_target.bl_preconditions in
      Symbols.Maps.iter (fun x (origin, target) ->
         try
            let source_version = try
               Symbols.Maps.find x jmp.jmp_versions
            with Not_found ->
               (* XXX: Is this ever reachable? *)
               Errors.semantic_error jmp.jmp_location
                  (String.capitalize (describe_symbol x)
                     ^ " must be initialised by now, but might not be.");
               report_liveness_origin x origin;
               raise Type_error
            in
            let t = coerce context (unsome source_version.ver_type) (unsome target.ver_type) in
            ignore t;
            preconditions :=
               List.map
                  (substv target (Var_v(jmp.jmp_location, source_version)))
                  !preconditions
         with Type_error -> ()
      ) jmp.jmp_target.bl_in;
      List.iter (prove state context jmp.jmp_location) !preconditions;
      Unit_type
   | Call_term(call, tail) ->
      begin match call.call_target.sym_info with
      | Subprogram_sym(subprogram_info) ->
         let preconditions = ref subprogram_info.sub_preconditions in
         let postconditions = ref subprogram_info.sub_postconditions in
         let (parameters: (symbol * expr option) array) = Array.of_list
            (List.map (fun parameter_sym ->
               (parameter_sym, None)) subprogram_info.sub_parameters)
         in
         let positional_args, named_args = call.call_arguments in
         let input_context = context in
         let output_context = ref context in
         let got_argument i (arg_in, arg_out) =
            match parameters.(i) with
               | (parameter_sym, None) ->
                  begin match parameter_sym.sym_info with Parameter_sym(mode, param_type) ->
                     begin match mode with
                        | Const_parameter | In_parameter ->
                           let arg_t = type_check_expr
                              {input_context with tc_expected = Some param_type} arg_in
                           in
                           preconditions := List.map
                              (subst parameter_sym arg_in) !preconditions;
                           parameters.(i) <- (parameter_sym, Some arg_in);
                           assign_to_lvalue !output_context arg_out arg_t;
                           output_context :=
                              {!output_context with
                                 tc_facts =
                                    Comparison(EQ, arg_in, arg_out)
                                       :: (!output_context).tc_facts};
                           postconditions := List.map
                              (subst parameter_sym arg_in) !postconditions
                        | Out_parameter ->
                           let arg_t = type_check_expr
                              {input_context with tc_expected = None} arg_in
                           in
                           ignore arg_t;
                           parameters.(i) <- (parameter_sym, Some arg_in);
                           assign_to_lvalue !output_context arg_out param_type;
                           postconditions := List.map
                              (subst parameter_sym arg_out) !postconditions
                        | In_out_parameter ->
                           let arg_t = type_check_expr
                              {input_context with tc_expected = Some param_type} arg_in
                           in
                           ignore arg_t;
                           preconditions := List.map
                              (subst parameter_sym arg_in) !preconditions;
                           parameters.(i) <- (parameter_sym, Some arg_in);
                           assign_to_lvalue !output_context arg_out param_type;
                           postconditions := List.map
                              (subst parameter_sym arg_out) !postconditions
                     end
                  end
               | (parameter_sym, Some _) ->
                  Errors.semantic_error call.call_location
                     ("Parameter `" ^ parameter_sym.sym_name
                        ^ "' specified twice.")
         in
         (* Bind positional arguments. *)
         list_iteri (fun i arg ->
            if i >= Array.length parameters then begin
               Errors.semantic_error call.call_location
                  ("Too many arguments to "
                     ^ describe_symbol call.call_target ^ ".")
            end else begin
               got_argument i arg
            end
         ) positional_args;
         (* Bind named arguments. *)
         List.iter (fun (name, arg) ->
            let rec search i =
               if i >= Array.length parameters then begin
                  Errors.semantic_error call.call_location
                     ("Parameter `" ^ name ^ "' doesn't exist in call to "
                        ^ describe_symbol call.call_target ^ ".")
               end else if (fst parameters.(i)).sym_name = name then begin
                  got_argument i arg
               end else begin
                  search (i + 1)
               end
            in search 0
         ) named_args;
         (* Check that all parameters have arguments. *)
         Array.iter (function
            | (_, Some _) -> ()
            | (parameter_sym, None) ->
               Errors.semantic_error call.call_location
                  ("Missing argument for parameter `" ^ parameter_sym.sym_name
                     ^ "' of " ^ describe_symbol call.call_target ^ ".")
         ) parameters;
         (* Prove that this subprogram's preconditions can be met, assuming
            the facts we know. *)
         List.iter (prove state input_context call.call_location) !preconditions;
         (* Store the argument binding for later translation stages. *)
         call.call_bound_arguments <-
            begin
               let rec loop bound_arguments = function
                  | 0 -> bound_arguments
                  | i ->
                     let _, Some arg = parameters.(i-1) in
                     loop (arg::bound_arguments) (i-1)
               in loop [] (Array.length parameters)
            end;
         (* Continue, assuming the postconditions. *)
         prerr_endline ("Postconditions after call: "
            ^ String.concat " and "
               (List.map string_of_expr !postconditions));
         type_check state
            {!output_context with
               tc_facts = !postconditions @ (!output_context).tc_facts}
            tail
      end
   | Static_assert_term(loc, expr, tail) ->
      ignore (type_check_expr
         {context with tc_expected = Some Boolean_type}
         expr);
      prove state context loc expr;
      type_check state context tail

let merge_types t1 t2 =
   try
      match t1, t2 with
         | Unit_type, Unit_type -> Unit_type
         | Boolean_type, Boolean_type -> Boolean_type
         | Integer_type, Integer_type -> Integer_type
   with (Match_failure _) as e ->
      prerr_endline ("merge_types: failed to merge `"
         ^ string_of_type t1 ^ "' with `"
         ^ string_of_type t2 ^ "'.");
      raise e

let resolve_unknowns_in_type
   (changed: bool ref)
   (t: ttype): ttype
= match t with
   | Unit_type | Boolean_type _ | Integer_type _ -> t
   | Unknown_type(unk) ->
      match unk.unk_incoming @ unk.unk_outgoing with
         | t::rest ->
            let merged_incoming = List.fold_left merge_types t rest in
            changed := true;
            merged_incoming
         | [] ->
            raise (Failure "resolve_unknowns_in_type")

let resolve_unknowns
   (changed: bool ref)
   (vars: ('a * symbol_v) Symbols.Maps.t):
   ('a * symbol_v) Symbols.Maps.t
=
   Symbols.Maps.map
      (fun (origin, x) ->
         x.ver_type <-
            Some (resolve_unknowns_in_type changed (unsome x.ver_type));
         (origin, x))
      vars

let type_check_blocks
   (blocks: block list)
   (entry_point: block)
   (parameters: (param_mode * ttype) Symbols.Maps.t)
=
   (* For each block, set unknown types for live variables. *)
   List.iter (fun block ->
      Symbols.Maps.iter (fun x (origin, xv) ->
         assert (xv.ver_symbol == x);
         match x.sym_info with
            | Parameter_sym(Out_parameter, _)
            | Variable_sym when block == entry_point ->
               (* Free at start of subprogram -> uninitialised. *)
               assert (match xv.ver_type with None -> true | Some _ -> false)
            | Parameter_sym((Const_parameter | In_parameter | In_out_parameter), _)
            | Variable_sym ->
               xv.ver_type <- Some (Unknown_type
                  {unk_incoming = [];
                   unk_outgoing = []});
      ) block.bl_in
   ) blocks;

   let first_pass = ref true in
   let finished = ref false in
   while not !finished do
      finished := true;
      List.iter (fun block ->
         let state = {
            ts_unsolved = [];
         } in
         let context = {
            tc_pass = if !first_pass then Guessing_pass else Checking_pass;
            tc_expected = Some Unit_type;
            tc_facts = block.bl_preconditions;
         } in
         let t = type_check state context (unsome block.bl_body) in
         ignore t;
         if !first_pass then begin
            first_pass := false;
            finished := false;
            let changed = ref true in
            while !changed do
               prerr_endline "Unknowns resolution iteration...";
               changed := false;
               List.iter (fun block ->
                  block.bl_in <-
                     resolve_unknowns changed block.bl_in
               ) blocks
            done
         end else begin
            List.iter (fun (loc, constr) ->
               if block == entry_point then begin
                  Errors.semantic_error loc
                     ("Cannot prove `"
                        ^ string_of_expr constr ^ "'.")
               end else begin
                  block.bl_preconditions <- constr :: block.bl_preconditions;
                  finished := false
               end
            ) state.ts_unsolved
         end
      ) blocks
   done;

   prerr_endline "";
   prerr_endline "Dumping blocks with computed types...";
   let f = Formatting.new_formatter () in
   dump_blocks f blocks;
   prerr_endline (Formatting.get_fmt_str f)
