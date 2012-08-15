open Symbols
open Icode
open Misc

type context = {
   tc_types    : Icode.context;
   tc_expected : ttype option;
}

type expr_context = expr -> expr

exception Type_error

type constraints = expr
let no_constraints = Boolean_literal true

let assert_unit t =
   assert (match t with
      | Unit_type -> true
      | _ -> false)

let quantify_type
   (t: ttype): expr_context * ttype
= match t with
   | Unit_type
   | Boolean_type(Constrained _)
   | Integer_type(Constrained _) -> (fun m -> m), t
   | Boolean_type(Unconstrained(Some original_sym)) ->
      let i = fresh_symbol original_sym in
      (fun m -> For_all(i,m)), Boolean_type(Constrained(Var i))
   | Integer_type(Unconstrained(Some original_sym)) ->
      let i = fresh_symbol original_sym in
      (fun m -> For_all(i,m)), Integer_type(Constrained(Var i))

let coerce t1 t2: constraints * ttype =
   try
      match t1, t2 with
         | Unit_type, Unit_type ->
            no_constraints, Unit_type
         | Boolean_type _, Boolean_type(Unconstrained _) ->
            no_constraints, t1
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
      | Some t2 -> coerce t t2

let rec type_check_expr
   (context: context)
   (expr: expr): constraints * ttype
= match expr with
   | Boolean_literal(b) ->
      got_type context
         (Boolean_type(Constrained(Boolean_literal(b))))
   | Integer_literal(i) ->
      got_type context
         (Integer_type(Constrained(Integer_literal(i))))
   | Var(x) ->
      got_type context
         (Symbols.Maps.find x context.tc_types)

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
      let constraint_context, src_major_type =
         quantify_type src_type
      in
      let tail_constr, tail_type =
         type_check
            {context with
               tc_types = Symbols.Maps.add
                  dest src_major_type context.tc_types}
            tail
      in
      (Conjunction [src_constr; constraint_context tail_constr]),
         tail_type
   | If_term(loc, condition, true_part, false_part) ->
      let condition_constr, condition_type =
         type_check_expr
            {context with
               tc_expected = Some (Boolean_type(Unconstrained(None)))}
            condition
      in
      let constr2, condition_type = quantify_type condition_type in
      let Boolean_type(Constrained(static_condition)) = condition_type in
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
      constr2 (Conjunction [
            condition_constr;
            Implication(
               Equal(static_condition, Boolean_literal true),
               true_part_constr);
            Implication(
               Equal(static_condition, Boolean_literal false),
               false_part_constr)
      ]), Unit_type
   | Jump_term(jmp) ->
      (* TODO! *)
      no_constraints, Unit_type

let type_check_blocks
   (blocks: block list)
   (entry_point: block)
   ((parameters, preconditions): Icode.context * expr list)
=
   List.iter (fun block ->
      let context = {
         tc_types =
            if block == entry_point then
               parameters
            else
               Symbols.Maps.empty;
         tc_expected = Some Unit_type;
      } in
      let constraints, t =
         type_check
            context
            (unsome block.bl_body)
      in
      prerr_endline (string_of_expr constraints)
   ) blocks
