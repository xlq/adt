open Symbols
open Icode
open Misc
open Big_int

type pass =
   (* Guessing pass - unknown types are guessed. *)
   | Guessing_pass
   (* Checking pass - unknown types are rejected. *)
   | Checking_pass
   (* Type checking during overloaded function resolution.
      No error messages must be output. The symbol table
      must not be mutated. *)
   | Overload_testing

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
   mutable ts_unsolved  : (constraint_origin * expr) list;
}

type type_error =
   | Type_mismatch of Lexing.position
                    * ttype (* expected *)
                    * ttype (* found *)
   | Uninitialised of Lexing.position
                    * symbol
   | Argument_not_lvalue of Lexing.position * symbol (* parameter *)
   | Argument_specified_twice of Lexing.position * symbol (* parameter *)
   | Too_many_arguments of Lexing.position * symbol (* subprogram *)
   | No_parameter_named of Lexing.position * string * symbol (* subprogram *)
   | Missing_argument_for_parameter of Lexing.position * symbol (* parameter *)

exception Type_error of type_error
exception Bail_out
exception Unresolved_unknown
exception Unsolved_constraint

let assert_unit t =
   assert (match t with
      | Unit_type -> true
      | _ -> false)

let report_type_error extra err =
   let extra = match extra with
      | Some s -> " " ^ s
      | None -> ""
   in
   match err with
      | Type_mismatch(loc, expected, found) ->
         Errors.semantic_error loc
            ("Expected type `"
               ^ string_of_type expected
               ^ "' but found type `"
               ^ string_of_type found ^ "'"
               ^ extra ^ ".")
      | Uninitialised(loc, x) ->
         Errors.semantic_error loc
            (String.capitalize (describe_symbol x)
               ^ " might not be initialised yet"
               ^ extra ^ ".")
      | Argument_not_lvalue(loc, parameter) ->
         Errors.semantic_error loc
            ("Argument for "
               ^ describe_symbol parameter
               ^ " must be a variable.")
      | Argument_specified_twice(loc, parameter) ->
         Errors.semantic_error loc
            ("Parameter `" ^ parameter.sym_name
               ^ "' specified twice.")
      | Too_many_arguments(loc, subprogram) ->
         Errors.semantic_error loc
            ("Too many arguments for "
               ^ describe_symbol subprogram)
      | No_parameter_named(loc, name, subprogram) ->
         Errors.semantic_error loc
            ("Parameter `" ^ name ^ "' doesn't exist in "
               ^ describe_symbol subprogram ^ ".")
      | Missing_argument_for_parameter(loc, parameter) ->
         Errors.semantic_error loc
            ("Missing argument for parameter `" ^ parameter.sym_name
               ^ "' of " ^ describe_symbol (unsome parameter.sym_parent) ^ ".")

let produce_type_error context err =
   match context.tc_pass with
      | Guessing_pass | Checking_pass ->
         report_type_error None err
      | Overload_testing ->
         raise (Type_error(err))

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
   | Boolean_literal(loc,b) -> Some(Boolean_literal(loc,not b))
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
      | Boolean_literal(_,b), Boolean_literal(_,b') -> b = b'
      | Integer_literal(_,i), Integer_literal(_,i') -> eq_big_int i i'
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
   (origin: constraint_origin)
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
            state.ts_unsolved <- (origin, to_prove) :: state.ts_unsolved
         with Fm_solver.Contradiction -> ()

let rec coerce context loc t1 t2: ttype =
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
            | Overload_testing ->
               t2
         end
      | t1, Unknown_type(unk) ->
         begin match context.tc_pass with
            | Guessing_pass ->
               prerr_endline "Coercing to Unknown_type.";
               unk.unk_incoming <- t1 :: unk.unk_incoming;
               t1
            | Checking_pass ->
               raise Unresolved_unknown
            | Overload_testing ->
               t1
         end
      | _ ->
         produce_type_error context
            (Type_mismatch(loc, t2, t1));
         t2

let got_type
   (context: context)
   (loc: Lexing.position)
   (t: ttype): ttype
=
   match context.tc_expected with
      | None -> t
      | Some t2 -> coerce context loc t t2

let rec type_check_expr
   (context: context)
   (expr: expr): ttype
= match expr with
   | Boolean_literal(loc,b) ->
      got_type context loc Boolean_type
   | Integer_literal(loc,i) ->
      got_type context loc Integer_type
   | Var_v(loc,x) ->
      begin match x.ver_type with
         | None ->
            produce_type_error context
               (Uninitialised(loc, x.ver_symbol));
            (match context.tc_expected with
               | Some t -> t
               | None -> Unit_type)
         | Some t ->
            got_type context loc t
      end
   | Comparison(op, lhs, rhs) ->
      let loc = loc_of_expression lhs in
      let operand_context = {context with tc_expected = None} in
      let lhs_t = type_check_expr operand_context lhs in
      let rhs_t = type_check_expr operand_context rhs in
      ignore (coerce context loc lhs_t rhs_t);
      got_type context loc Boolean_type

let rec bind_pre_post_condition (post: bool) e =
   let r = bind_pre_post_condition post in
   match e with
      | Boolean_literal _
      | Integer_literal _ -> e
      | Var(loc, param) ->
         begin match param.sym_info with Parameter_sym(mode, t) ->
            let available = match mode with
               | Const_parameter | In_parameter | In_out_parameter -> true
               | Out_parameter -> post
            in
            if available then begin
               Var_v(loc,
                  {ver_symbol = param;
                   ver_number = -1;
                   ver_type = Some t;
                   ver_next = None})
            end else begin
               Errors.semantic_error loc
                  (String.capitalize (describe_symbol param)
                     ^ " is not available in a "
                     ^ (if post then "post-" else "pre-") ^ "condition.");
               e
            end
         end
      | Negation(e) -> Negation(r e)
      | Comparison(op, lhs, rhs) -> Comparison(op, r lhs, r rhs)

let type_check_subprogram_declaration info =
   let context =
      {
         tc_pass = Checking_pass;
         tc_expected = Some Boolean_type;
         tc_facts = [];
      }
   in
   List.iter
      (fun constr ->
         ignore
            (type_check_expr context
               (bind_pre_post_condition false constr)))
      info.sub_preconditions;
   List.iter
      (fun constr ->
         ignore
            (type_check_expr context
               (bind_pre_post_condition true constr)))
      info.sub_postconditions

let assign_to_lvalue
   (context: context)
   (dest: expr)
   (src_type: ttype)
= match dest with
   | Var_v(_, x) -> x.ver_type <- Some src_type

type candidate =
   {
      mutable can_rejected       : (symbol option * type_error) option;
      mutable can_symbol         : symbol;
      mutable can_info           : subprogram_info;
      can_parameters             : (symbol * (expr * expr option) option) array;
      mutable can_preconditions  : expr list;
      mutable can_postconditions : expr list;
      mutable can_extra_facts    : expr list;
   }

let for_parameter = function
   | None -> None
   | Some parameter ->
      Some ("for parameter `" ^ parameter.sym_name ^ "'")

let rec type_check
   (state: state)
   (context: context)
   (iterm: iterm): ttype
= match iterm with
   | Return_term(ret) ->
      begin match ret.ret_subprogram.sym_info with Subprogram_sym(info) ->
         let postconditions = ref info.sub_postconditions in
         List.iter (fun param ->
            match param.sym_info with
               | Parameter_sym((Out_parameter | In_out_parameter), t) ->
                  let src_version = Symbols.Maps.find param ret.ret_versions in
                  ignore
                     (coerce context ret.ret_location
                        (unsome src_version.ver_type) t);
                  postconditions :=
                     List.map (subst param (Var_v(ret.ret_location, src_version)))
                        !postconditions;
               | Parameter_sym((Const_parameter | In_parameter), _) -> ()
         ) info.sub_parameters;
         List.iter (fun constr ->
            prove state context
               (From_postconditions(ret.ret_location, ret.ret_subprogram))
               constr
         ) !postconditions
      end;
      got_type context ret.ret_location Unit_type
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
   (*
   | Jump_term(jmp) ->
      let preconditions = ref jmp.jmp_target.bl_preconditions in
      Symbols.Maps.iter (fun x target ->
         try
            let source_version = try
               Symbols.Maps.find x jmp.jmp_versions
            with Not_found ->
               (* XXX: Is this ever reachable? *)
               prerr_endline "YES, THIS IS REACHABLE.";
               Errors.semantic_error jmp.jmp_location
                  (String.capitalize (describe_symbol x)
                     ^ " must be initialised by now, but might not be.");
               raise Bail_out
            in
            ignore (coerce context jmp.jmp_location
               (unsome source_version.ver_type)
               (unsome target.ver_type));
            preconditions :=
               List.map
                  (fun (origin, constr) ->
                     (origin,
                      substv target
                        (Var_v(jmp.jmp_location, source_version))
                        constr))
                  !preconditions
         with Bail_out -> ()
      ) jmp.jmp_target.bl_in;
      List.iter
         (fun (origin, constr) ->
            prove state context origin constr)
         !preconditions;
      Unit_type
   | Call_term(call, tail) ->
      (* Assemble a list of successful candidate subprograms. *)
      let candidates = List.map
         (fun subprogram_sym ->
            match subprogram_sym.sym_info with Subprogram_sym(subprogram_info) ->
               {
                  can_rejected      = None;
                  can_symbol        = subprogram_sym;
                  can_info          = subprogram_info;
                  can_parameters    = Array.of_list
                     (List.map (fun parameter_sym -> (parameter_sym, None))
                        subprogram_info.sub_parameters);
                  can_preconditions = subprogram_info.sub_preconditions;
                  can_postconditions= subprogram_info.sub_postconditions;
                  can_extra_facts   = [];
               }
         ) call.call_candidates
      in
      assert (match candidates with | [] -> false | _ -> true);
      let reject_candidate candidate (parameter: symbol option) (reason: type_error) =
         candidate.can_rejected <- Some (parameter, reason);
         (* If that was the last candidate, it's time to report some errors. *)
         if List.for_all (fun other_candidate ->
            match other_candidate.can_rejected with
               | Some _ -> true
               | None -> false) candidates
         then begin
            begin match candidates with
               | [x] ->
                  assert (x == candidate); (* of course *)
                  report_type_error
                     (for_parameter parameter)
                     reason
               | x::_ ->
                  Errors.semantic_error call.call_location
                     ("No definition of `" ^ x.can_symbol.sym_name
                        ^ "' matches these arguments.");
                  List.iter (fun candidate ->
                     match candidate.can_rejected with Some (parameter, reason) ->
                        match candidate.can_symbol.sym_declared with Some loc ->
                           Errors.semantic_error loc
                              ("This definition of `"
                                 ^ x.can_symbol.sym_name ^ "' doesn't match because:");
                           report_type_error
                              (for_parameter parameter)
                              reason
                  ) candidates
            end;
            raise Bail_out
         end
      in
      let positional_args, named_args = call.call_arguments in
      let input_context = context in
      let context = () in ignore(context);
      let got_argument candidate i (arg_in, arg_out) =
         match candidate.can_parameters.(i) with
            | (parameter_sym, None) ->
               (* Mark parameter as matched. *)
               candidate.can_parameters.(i) <- (parameter_sym, Some(arg_in, arg_out));
               begin match parameter_sym.sym_info with
               | Parameter_sym(param_mode, param_type) ->
                  try
                     (* Input parameter. *)
                     begin match param_mode with
                        | Const_parameter | In_parameter | In_out_parameter ->
                           ignore (type_check_expr
                              {input_context with
                                 tc_expected = Some param_type;
                                 tc_pass = Overload_testing}
                              arg_in);
                           candidate.can_preconditions <-
                              List.map (subst parameter_sym arg_in)
                                 candidate.can_preconditions;
                        | Out_parameter -> ()
                     end;
                     (* Output parameter. *)
                     begin match param_mode with
                        | Const_parameter | In_parameter ->
                           begin match arg_out with
                              | Some arg_out ->
                                 (* The argument was a valid L-value but was not
                                    matched to an "in" or "in out" parameter.
                                    Set the type of arg_out and record that
                                    arg_in and arg_out are equal. *)
                                 (* TODO: assign_to_lvalue context arg_out arg_in_t *)
                                 candidate.can_extra_facts <-
                                    Comparison(EQ, arg_in, arg_out)
                                       :: candidate.can_extra_facts
                              | None -> ()
                           end
                        | In_out_parameter | Out_parameter ->
                           begin match arg_out with
                              | None ->
                                 reject_candidate candidate (Some parameter_sym)
                                    (Argument_not_lvalue(loc_of_expression arg_in,
                                       parameter_sym))
                              | Some arg_out ->
                                 ignore (type_check_expr
                                    {input_context with
                                       tc_expected = None;
                                       tc_pass = Overload_testing}
                                    arg_in);
                                 (* TODO: assign_to_lvalue arg_out param_type *)
                                 candidate.can_postconditions <-
                                    List.map (subst parameter_sym arg_out)
                                       candidate.can_postconditions
                           end
                     end
                  with Type_error error ->
                     reject_candidate candidate (Some parameter_sym) error
               end
            | (parameter_sym, Some _) ->
               reject_candidate candidate (Some parameter_sym)
                  (Argument_specified_twice(loc_of_expression arg_in,
                     parameter_sym))
      in
      (* Process positional arguments. *)
      list_iteri (fun i arg ->
         List.iter (fun candidate ->
            match candidate.can_rejected with
               | None ->
                  if i >= Array.length candidate.can_parameters then begin
                     reject_candidate candidate None
                        (Too_many_arguments(
                           call.call_location,
                           candidate.can_symbol))
                  end else begin
                     got_argument candidate i arg
                  end
               | Some _ -> ()
         ) candidates;
      ) positional_args;
      (* Process named arguments. *)
      List.iter (fun (name, arg) ->
         List.iter (fun candidate ->
            match candidate.can_rejected with
               | None ->
                  let rec search i =
                     if i >= Array.length candidate.can_parameters then
                        reject_candidate candidate None
                           (No_parameter_named(
                              loc_of_expression (fst arg),
                              name,
                              candidate.can_symbol))
                     else if (fst candidate.can_parameters.(i)).sym_name = name
                     then
                        got_argument candidate i arg
                     else
                        search (i + 1)
                  in search 0
               | Some _ -> ()
         ) candidates
      ) named_args;
      (* Check that all parameters have arguments. *)
      List.iter (fun candidate ->
         Array.iter (function
            | (_, Some _) -> ()
            | (parameter, None) ->
               reject_candidate candidate (Some parameter)
                  (Missing_argument_for_parameter(call.call_location, parameter))
         ) candidate.can_parameters
      ) candidates;
      let remaining_candidates = List.filter (fun candidate ->
         match candidate.can_rejected with
            | None -> true
            | Some _ -> false
         ) candidates
      in
      begin match remaining_candidates with
         | [candidate] ->
            prerr_endline ("Chose `"
               ^ candidate.can_symbol.sym_name ^ "' at "
               ^ Errors.string_of_location (unsome candidate.can_symbol.sym_declared)
               ^ ".");
            List.iter (fun precondition ->
               prove state input_context
                  (From_preconditions(
                     Symbols.loc_of_expression precondition,
                     candidate.can_symbol))
                  precondition)
               candidate.can_preconditions;
            (* TODO: Store argument binding. *)
            Array.iter (function
               | {sym_info =
                     Parameter_sym((Out_parameter|In_out_parameter),t)},
                 Some(arg_in, Some arg_out)
               ->
                  assign_to_lvalue input_context arg_out t
               | ({sym_info = Parameter_sym(_,_)}, _) -> ()
            ) candidate.can_parameters;
            let output_context = {input_context with
               tc_facts = List.rev_append
                  candidate.can_postconditions
                  (List.rev_append
                     candidate.can_extra_facts
                     input_context.tc_facts)}
            in
            type_check state output_context tail
         | first::_ ->
            begin match input_context.tc_pass with
               | Guessing_pass -> ()
               | Checking_pass ->
                  Errors.semantic_error call.call_location
                     ("Ambiguous call of overloaded subprogram `"
                        ^ first.can_symbol.sym_name ^ "'.");
                  List.iter (fun candidate ->
                     Errors.semantic_error
                        (unsome candidate.can_symbol.sym_declared)
                        ("This definition matches.")
                  ) remaining_candidates
            end;
            type_check state input_context tail
      end;
   *)
   | Static_assert_term(loc, expr, tail) ->
      ignore (type_check_expr
         {context with tc_expected = Some Boolean_type}
         expr);
      prove state context (From_static_assertion loc) expr;
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
         begin try
            x.ver_type <-
               Some (resolve_unknowns_in_type changed (unsome x.ver_type))
         with Failure "resolve_unknowns_in_type" ->
            raise (Failure ("resolve_unknowns_in_type: "
               ^ describe_symbol x.ver_symbol))
         end;
         (origin, x))
      vars

let type_check_blocks
   (blocks: block list)
   (entry_point: block)
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
            | Parameter_sym((Const_parameter | In_parameter | In_out_parameter), t) ->
               xv.ver_type <- Some t
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
            tc_facts = List.map snd block.bl_preconditions;
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
            List.iter (fun (origin, constr) ->
               if block == entry_point then begin
                  Errors.semantic_error
                     (loc_of_constraint_origin origin)
                     ("Cannot prove `"
                        ^ string_of_expr constr ^ "', "
                        ^ describe_constraint_origin origin ^ ".");
                  Errors.semantic_error
                     (loc_of_expression constr)
                     ("Original constraint was here.")
               end else begin
                  block.bl_preconditions <- (origin, constr) :: block.bl_preconditions;
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
