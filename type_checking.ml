open Symbols
open Icode
open Misc

type pass =
   | Guessing_pass
   | Checking_pass

type context = {
   tc_pass     : pass;
   tc_vars     : (ttype * version) Symbols.Maps.t;
   tc_expected : ttype option;
}

type expr_context = expr -> expr

exception Type_error

exception Unresolved_unknown

type constraints = expr
let no_constraints = Boolean_literal true

let assert_unit t =
   assert (match t with
      | Unit_type -> true
      | _ -> false)

let quantify
   (vars: (ttype * version) Symbols.Maps.t)
   (constr: constraints): constraints
=
   Symbols.Maps.fold
      (fun parameter_sym (parameter_type, parameter_version) constr ->
         For_all(parameter_sym, parameter_version, constr))
      vars constr

let rec coerce context t1 t2: constraints * ttype =
   try
      match t1, t2 with
         | Unit_type, Unit_type ->
            no_constraints, Unit_type
         | Boolean_type, Boolean_type ->
            no_constraints, t1
         | Unknown_type(unk), t2 ->
            begin match context.tc_pass with
               | Guessing_pass ->
                  prerr_endline "Coercing from Unknown_type.";
                  unk.unk_outgoing <- t2 :: unk.unk_outgoing;
                  no_constraints, t2
               | Checking_pass ->
                  raise Unresolved_unknown
            end
         | t1, Unknown_type(unk) ->
            begin match context.tc_pass with
               | Guessing_pass ->
                  prerr_endline "Coercing to Unknown_type.";
                  unk.unk_incoming <- t1 :: unk.unk_incoming;
                  no_constraints, t1
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
   (t: ttype): constraints * ttype
=
   match context.tc_expected with
      | None -> (no_constraints, t)
      | Some t2 -> coerce context t t2

let rec type_check_expr
   (context: context)
   (expr: expr): constraints * ttype
= match expr with
   | Boolean_literal(b) ->
      got_type context Boolean_type
   | Integer_literal(i) ->
      got_type context Integer_type
   | Var(x) ->
      let t, version = Symbols.Maps.find x context.tc_vars in
      got_type context t

let rec type_check
   (context: context)
   (iterm: iterm): constraints * ttype
= match iterm with
   | Null_term(loc) ->
      got_type context Unit_type
   | Assignment_term(loc, dest, src, tail) ->
      let src_constr, src_type =
         type_check_expr
            {context with tc_expected = None}
            src
      in
      let tail_constr, tail_type =
         type_check
            {context with
               tc_vars = Symbols.Maps.add
                  dest (src_type, new_version dest) context.tc_vars}
            tail
      in
      (Conjunction [src_constr; tail_constr]),
         tail_type
   | If_term(loc, condition, true_part, false_part) ->
      let condition_constr, condition_type =
         type_check_expr
            {context with
               tc_expected = Some Boolean_type}
            condition
      in
      let true_part_constr, true_part_type =
         type_check context true_part
      in
      let false_part_constr, false_part_type =
         type_check context false_part
      in
      assert_unit true_part_type;
      assert_unit false_part_type;
      begin match context.tc_expected with
         | None -> ()
         | Some t -> assert_unit t
      end;
      (Conjunction [
            condition_constr;
            Implication(
               Equal(condition, Boolean_literal true),
               true_part_constr);
            Implication(
               Equal(condition, Boolean_literal false),
               false_part_constr)
      ]), Unit_type
   | Jump_term(jmp) ->
      let constraints =
         Symbols.Maps.fold (fun x (target_t, target_version) constraints ->
            let source_t, source_version = Symbols.Maps.find x context.tc_vars in
            prerr_endline ("Jump_term: coercing `"
               ^ string_of_type source_t ^ "' to `"
               ^ string_of_type target_t ^ "'.");
            let coerce_constr, t = coerce context source_t target_t in
            coerce_constr::constraints
         ) jmp.jmp_target.bl_in []
      in
      Conjunction constraints, Unit_type
   | Static_assert_term(loc, expr, tail) ->
      let expr_constr, expr_t =
         type_check_expr
            {context with
               tc_expected =
                  Some Boolean_type}
            expr
      in
      let constr, t = type_check context tail in
      Conjunction [expr_constr; expr; constr], t

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
      } in
      let constraints, t =
         type_check
            context
            (unsome block.bl_body)
      in
      ignore(constraints, t)
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
      } in
      let constraints, t =
         type_check
            context
            (unsome block.bl_body)
      in
      let constraints = quantify block.bl_in constraints in
      prerr_endline ("Constraints: "
         ^ string_of_expr constraints)
   ) blocks
