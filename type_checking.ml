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
   tc_vars     : (ttype * version) Symbols.Maps.t;
   (* The type that's expected of the term or expression being
      typed under this context. *)
   tc_expected : ttype option;
   (* Boolean expressions known true. *)
   tc_facts    : expr list;
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
   (get_version : symbol -> version)
   (e: expr): expr
=
   let r = bind_versions get_version in
   match e with
   | Boolean_literal _
   | Integer_literal _
   | Var_version _ -> e
   | Var(x) -> Var_version(x, get_version x)
   | Comparison(op, lhs, rhs) ->
      Comparison(op, r lhs, r rhs)

let negate = function
   | Boolean_literal(b) -> Some(Boolean_literal(not b))
   | Integer_literal _ | Var _ | Var_version _ -> None
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
      | Var _ | Var_version _ -> e
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
      | Var_version(x,v), Var_version(x',v') ->
         (x == x') && (v = v')
      | Negation(x), Negation(x') -> expressions_match x x'
      | Comparison(op, lhs, rhs), Comparison(op', lhs', rhs') ->
         (op = op') && (expressions_match lhs lhs')
                    && (expressions_match rhs rhs')
      | Boolean_literal _, _ | _, Boolean_literal _
      | Integer_literal _, _ | _, Integer_literal _
      | Var_version _, _ | _, Var_version _
      | Negation _, _ | _, Negation _
      | Comparison _, _ | _, Comparison _ ->
         false

let prove
   (context: context)
   (e: expr): unit
=
   let facts = List.map normalise context.tc_facts in
   let e = normalise e in
   (*
   prerr_endline ("Must prove "
      ^ string_of_expr e
      ^ " under the assumptions: "
      ^ String.concat " and "
         (List.map string_of_expr facts));
   *)
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
         try Fm_solver.solve inequalities
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
   | Var(x) ->
      let t, version = Symbols.Maps.find x context.tc_vars in
      let t = got_type context t in
      Var_version(x, version), t
   | Comparison(op, lhs, rhs) ->
      let operand_context = {context with tc_expected = None} in
      let lhs, lhs_t = type_check_expr operand_context lhs in
      let rhs, rhs_t = type_check_expr operand_context rhs in
      let _ = coerce context lhs_t rhs_t in
      let result_t = got_type context Boolean_type in
      (Comparison(op, lhs, rhs), result_t)

let rec type_check
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
      let dest_version = new_version dest in
      type_check
         {context with
            tc_vars = Symbols.Maps.add
               dest (src_type, dest_version) context.tc_vars;
            tc_facts =
               Comparison(EQ, Var_version(dest, dest_version), src)
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
            {context with
               tc_facts = condition :: context.tc_facts}
            true_part
      in
      let false_part_type =
         type_check
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
      Symbols.Maps.iter (fun x (target_t, target_version) ->
         let source_t, source_version = Symbols.Maps.find x context.tc_vars in
         let t = coerce context source_t target_t in
         ignore t
      ) jmp.jmp_target.bl_in;
      Unit_type
   | Static_assert_term(loc, expr, tail) ->
      let expr, expr_t =
         type_check_expr
            {context with tc_expected = Some Boolean_type}
            expr
      in
      begin try prove context expr
      with Unsolved_constraint ->
         Errors.semantic_error loc
            ("Static assertion could not be proved: `"
               ^ string_of_expr expr ^ "'.")
      end;
      type_check context tail

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
   (vars: (ttype * version) Symbols.Maps.t):
   (ttype * version) Symbols.Maps.t
=
   Symbols.Maps.map
      (fun (t, version) -> (resolve_unknowns_in_type changed t, version))
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
                  (parameter_type, new_version parameter_sym))
               parameters
         end else begin
            Symbols.Maps.empty
         end
      in
      block.bl_in <-
         Symbols.Sets.fold (fun parameter_sym vars ->
            if Symbols.Maps.mem parameter_sym vars then begin
               vars
            end else begin
               Symbols.Maps.add parameter_sym
                  ((Unknown_type
                     {unk_incoming = [];
                      unk_outgoing = []}),
                   new_version parameter_sym)
                  vars
            end
         ) block.bl_free initial_vars
   ) blocks;

   (* First pass: guess unknowns. *)
   List.iter (fun block ->
      let context = {
         tc_pass     = Guessing_pass;
         tc_vars     = block.bl_in;
         tc_expected = Some Unit_type;
         tc_facts    = List.map
            (bind_versions (fun x -> snd (Symbols.Maps.find x block.bl_in)))
            block.bl_preconditions;
      } in
      let t =
         type_check
            context
            (unsome block.bl_body)
      in
      ignore t
   ) blocks;
   let changed = ref true in
   while !changed do
      prerr_endline "Start of iteration.";
      changed := false;
      List.iter (fun block ->
         block.bl_in <-
            resolve_unknowns changed block.bl_in
      ) blocks
   done;

   prerr_endline "Dumping blocks with computed types...";
   let f = Formatting.new_formatter () in
   dump_blocks f blocks;
   prerr_endline (Formatting.get_fmt_str f);

   (* Second pass: check types. *)
   prerr_endline "Generating constraints.";
   List.iter (fun block ->
      let context = {
         tc_pass     = Checking_pass;
         tc_vars     = block.bl_in;
         tc_expected = Some Unit_type;
         tc_facts    = List.map
            (bind_versions (fun x -> snd (Symbols.Maps.find x block.bl_in)))
            block.bl_preconditions;
      } in
      let t =
         type_check
            context
            (unsome block.bl_body)
      in
      ignore t
   ) blocks
