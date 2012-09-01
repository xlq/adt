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
   (* The types and current versions of variables. *)
   tc_vars     : symbol_v Symbols.Maps.t;
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

(* Get versions for the variables in the given expression.
   I.e. change all Var to Var_version. *)
let rec bind_versions
   (get_version : symbol -> symbol_v)
   (e: expr): expr
=
   let r = bind_versions get_version in
   match e with
   | Boolean_literal _
   | Integer_literal _
   | Var_v _ -> e
   | Var(_,x) -> Var_v(get_version x)
   | Comparison(op, lhs, rhs) ->
      Comparison(op, r lhs, r rhs)

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
      | Var_v(x') when x == x' -> replacement
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
      | Var_v(x), Var_v(x') -> x == x'
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

let prove
   (state: state)
   (context: context)
   (loc: Lexing.position)
   (to_prove: expr): unit
=
   let facts = List.map normalise context.tc_facts in
   let e = normalise to_prove in
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
   (expr: expr): expr * ttype
= match expr with
   | Boolean_literal(b) ->
      let t = got_type context Boolean_type in
      Boolean_literal(b), t
   | Integer_literal(i) ->
      let t = got_type context Integer_type in
      Integer_literal(i), t
   | Var(loc,x) ->
      let x' = try
         Symbols.Maps.find x context.tc_vars
      with Not_found ->
         Errors.semantic_error loc
            (String.capitalize (describe_symbol x)
               ^ " might not be initialised yet.");
         raise Type_error
      in
      let t = got_type context (unsome x'.ver_type) in
      Var_v(x'), t
   | Comparison(op, lhs, rhs) ->
      let operand_context = {context with tc_expected = None} in
      let lhs, lhs_t = type_check_expr operand_context lhs in
      let rhs, rhs_t = type_check_expr operand_context rhs in
      let _ = coerce context lhs_t rhs_t in
      let result_t = got_type context Boolean_type in
      (Comparison(op, lhs, rhs), result_t)

let rec type_check
   (state: state)
   (context: context)
   (iterm: iterm): ttype
= match iterm with
   | Null_term(loc) ->
      got_type context Unit_type
   | Assignment_term(loc, dest, src, tail) ->
      let src, src_type =
         type_check_expr
            {context with tc_expected = None}
            src
      in
      dest.ver_type <- Some src_type;
      type_check
         state
         {context with
            tc_vars = Symbols.Maps.add
               dest.ver_symbol dest context.tc_vars;
            tc_facts =
               Comparison(EQ, Var_v(dest), src)
                  :: context.tc_facts}
         tail
   | If_term(loc, condition, true_part, false_part) ->
      let condition, condition_type =
         type_check_expr
            {context with
               tc_expected = Some Boolean_type}
            condition
      in
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
      Symbols.Maps.iter (fun x target ->
         try
            let source_version = try
               Symbols.Maps.find x context.tc_vars
            with Not_found ->
               Errors.semantic_error jmp.jmp_location
                  (String.capitalize (describe_symbol x)
                     ^ " must be initialised by now, but might not be.");
               raise Type_error
            in
            let t = coerce context (unsome source_version.ver_type) (unsome target.ver_type) in
            ignore t;
            preconditions :=
               List.map
                  (substv target (Var_v(source_version)))
                  !preconditions
         with Type_error -> ()
      ) jmp.jmp_target.bl_in;
      List.iter (prove state context jmp.jmp_location) !preconditions;
      Unit_type
   | Call_term(call, tail) ->
      begin match call.call_target.sym_info with
      | Subprogram_sym(subprogram_info) ->
         let preconditions = ref subprogram_info.sub_preconditions in
         let (parameters: (symbol * expr option) array) = Array.of_list
            (List.map (fun parameter_sym ->
               (parameter_sym, None)) subprogram_info.sub_parameters)
         in
         let positional_args, named_args = call.call_arguments in
         let got_argument i arg =
            match parameters.(i) with
               | (parameter_sym, None) ->
                  begin
                     match parameter_sym.sym_info with Parameter_sym(param_type) ->
                     let arg, arg_t = type_check_expr
                        {context with tc_expected = Some param_type} arg
                     in
                     ignore arg_t;
                     preconditions := List.map (subst parameter_sym arg) !preconditions;
                     parameters.(i) <- (parameter_sym, Some arg)
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
         List.iter (prove state context call.call_location) !preconditions;
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
         type_check state context tail
      end
   | Static_assert_term(loc, expr, tail) ->
      let expr, expr_t =
         type_check_expr
            {context with tc_expected = Some Boolean_type}
            expr
      in
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
   (vars: symbol_v Symbols.Maps.t):
   symbol_v Symbols.Maps.t
=
   Symbols.Maps.map
      (fun x ->
         x.ver_type <-
            Some (resolve_unknowns_in_type changed (unsome x.ver_type));
         x)
      vars

let type_check_blocks
   (blocks: block list)
   (entry_point: block)
   (parameters: ttype Symbols.Maps.t)
=
   (* For each block, create a new context with unknown types
      for live variables. *)
   List.iter (fun block ->
      let initial_vars =
         if block == entry_point then begin
            Symbols.Maps.mapi
               (fun parameter_sym parameter_type ->
                  let param' = new_version parameter_sym in
                  param'.ver_type <- Some parameter_type;
                  param')
               parameters
         end else begin
            Symbols.Maps.empty
         end
      in
      block.bl_in <-
         Symbols.Sets.fold (fun x vars ->
            if Symbols.Maps.mem x vars then begin
               vars
            end else begin
               if (block == entry_point) &&
                  (match x.sym_info with Parameter_sym _ -> false | _ -> true)
               then begin
                  (* This is free at the start of the subprogram.
                     It is therefore uninitialised. *)
                  vars
               end else begin
                  let xv = new_version x in
                  let t = Unknown_type
                     {unk_incoming = [];
                      unk_outgoing = []}
                  in
                  xv.ver_type <- Some t;
                  Symbols.Maps.add x xv vars
               end;
            end
         ) block.bl_free initial_vars
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
            tc_vars = block.bl_in;
            tc_expected = Some Unit_type;
            tc_facts = List.map
               (bind_versions (fun x -> Symbols.Maps.find x block.bl_in))
               block.bl_preconditions;
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
