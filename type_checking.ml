open Symbols
open Icode
open Misc

type pass =
   | Guessing_pass
   | Checking_pass

type context = {
   tc_pass     : pass;
   tc_types    : Icode.context;
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

(* Given a closed type, extracts the existential quantifications
   from the type and returns a constraint context with the extracted
   quantifications, and the type without the quantifications. *)
let rec quantify_type
   (context: context)
   (t: ttype): expr_context * ttype
=
   try
      match t with
      | Unit_type
      | Boolean_type(Constrained _)
      | Integer_type(Constrained _) -> (fun m -> m), t
      | Boolean_type(Unconstrained(Some original_sym)) ->
         let i = fresh_symbol original_sym in
         (fun m -> For_all(i,m)), Boolean_type(Constrained(Var i))
      | Integer_type(Unconstrained(Some original_sym)) ->
         let i = fresh_symbol original_sym in
         (fun m -> For_all(i,m)), Integer_type(Constrained(Var i))
      | Unknown_type(unk) ->
         begin match context.tc_pass with
            | Guessing_pass ->
               prerr_endline "Unknown_type in quantify_type.";
               (fun m -> m), t
            | Checking_pass ->
               raise Unresolved_unknown
         end
   with (Match_failure _) as e ->
      prerr_endline ("quantify_type: Match_failure: `"
         ^ string_of_type t ^ "'.");
      raise e

(* Find a symbol that describes this expression.
   This is to make constraints easier for humans to follow.
   Hopefully. *)
let rec find_descriptive_sym = function
   | Boolean_literal _
   | Integer_literal _
   | Equal _
   | Conjunction _
   | Implication _ -> None
   | Var(x) -> Some x
   | For_all(_,e) -> find_descriptive_sym e

let close_disc context = function
   | Unconstrained(sym) -> Unconstrained(sym)
   | Constrained(i) ->
      Unconstrained(find_descriptive_sym i) (* TODO: More precise! *)

(* Given an open type under the given context,
   return a closed type. This is used for guessing unknowns. *)
let close_type context = function
   | Unknown_type(unk) -> raise (Failure "close_type")
   | Unit_type -> Unit_type
   | Boolean_type(i) -> Boolean_type(close_disc context i)
   | Integer_type(i) -> Integer_type(close_disc context i)

let rec coerce context t1 t2: constraints * ttype =
   try
      match t1, t2 with
         | Unit_type, Unit_type ->
            no_constraints, Unit_type
         | Boolean_type _, Boolean_type(Unconstrained _) ->
            no_constraints, t1
         | Boolean_type(Constrained i), Boolean_type(Constrained j) ->
            (Equal(i, j)), t2
         | Unknown_type(unk), t2 ->
            begin match context.tc_pass with
               | Guessing_pass ->
                  prerr_endline "Coercing from Unknown_type.";
                  unk.unk_outgoing <- (close_type context t2) :: unk.unk_outgoing;
                  no_constraints, t2
               | Checking_pass ->
                  raise Unresolved_unknown
            end
         | t1, Unknown_type(unk) ->
            begin match context.tc_pass with
               | Guessing_pass ->
                  prerr_endline "Coercing to Unknown_type.";
                  unk.unk_incoming <- (close_type context t1) :: unk.unk_incoming;
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
         quantify_type context src_type
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
      let constr2, condition_type = quantify_type context condition_type in
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
      let quants, constraints =
         Symbols.Maps.fold (fun x target_t (quants, constraints) ->
            let source_t = Symbols.Maps.find x context.tc_types in
            prerr_endline ("Jump_term: coercing `"
               ^ string_of_type source_t ^ "' to `"
               ^ string_of_type target_t ^ "'.");
            let coerce_constr, t = coerce context source_t target_t in
            let quant, t = quantify_type context t in
            quant::quants, coerce_constr::constraints
         ) jmp.jmp_target.bl_free_types ([], [])
      in
      List.fold_left (fun constr quant -> quant constr)
         (Conjunction(constraints)) quants, Unit_type
   | Static_assert_term(loc, expr, tail) ->
      let expr_constr, expr_t =
         type_check_expr
            {context with
               tc_expected =
                  Some(Boolean_type(Constrained(Boolean_literal(true))))}
            expr
      in
      let constr, t = type_check context tail in
      Conjunction [expr_constr; constr], t

let merge_types t1 t2 =
   try
      match t1, t2 with
         | Unit_type, Unit_type -> Unit_type
         | Boolean_type(Unconstrained sym), Boolean_type(_)
         | Boolean_type(_), Boolean_type(Unconstrained sym) ->
            Boolean_type(Unconstrained sym)
         | Boolean_type(Constrained(Var i)), Boolean_type(Constrained(Var j)) when i == j ->
            (* XXX: This case is too special. *)
            Boolean_type(Constrained(Var i))
         | Integer_type(Unconstrained sym), Integer_type(_)
         | Integer_type(_), Integer_type(Unconstrained sym) ->
            Integer_type(Unconstrained sym)
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
   (types: ttype Symbols.Maps.t):
   ttype Symbols.Maps.t
=
   Symbols.Maps.map
      (resolve_unknowns_in_type changed)
      types

let type_check_blocks
   (blocks: block list)
   (entry_point: block)
   (parameters: Icode.context)
=
   (* For each block, create a new context with unknown types
      for live variables. *)
   List.iter (fun block ->
      let initial_types =
         if block == entry_point then
            parameters
         else
            Symbols.Maps.empty
      in
      block.bl_free_types <-
         Symbols.Sets.fold (fun x types ->
            if Symbols.Maps.mem x types then begin
               types
            end else begin
               Symbols.Maps.add x
                  (Unknown_type
                     {unk_incoming = [];
                      unk_outgoing = []})
                  types
            end
         ) block.bl_free initial_types
   ) blocks;

   (* First pass: guess unknowns. *)
   List.iter (fun block ->
      let context = {
         tc_pass     = Guessing_pass;
         tc_types    = block.bl_free_types;
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
         block.bl_free_types <-
            resolve_unknowns changed block.bl_free_types
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
         tc_types    = block.bl_free_types;
         tc_expected = Some Unit_type;
      } in
      let constraints, t =
         type_check
            context
            (unsome block.bl_body)
      in
      prerr_endline ("Constraints: "
         ^ string_of_expr constraints)
   ) blocks
