open Symbols
open Icode
open Big_int
open Misc

type context = {
   (* List of unsolved constraints. *)
   cc_unsolved    : (constraint_origin * expr) list ref;
   (* Boolean expressions known to be true. *)
   cc_facts       : expr list;
}

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
      | Boolean_literal _ -> expr
      | Integer_literal _ -> expr
      | Var_v(_,x') when x == x' -> replacement
      | Var_v _ -> expr
      | Negation(e) -> Negation(r e)
      | Comparison(op, lhs, rhs) -> Comparison(op, r lhs, r rhs)

(* Negate a boolean expression. *)
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
   (context: context)
   (origin: constraint_origin)
   (to_prove: expr): unit
=
   prerr_endline ("Proving "
      ^ string_of_expr to_prove
      ^ " under assumptions "
      ^ String.concat " and "
         (List.map string_of_expr context.cc_facts));
   let facts = List.map normalise context.cc_facts in
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
            context.cc_unsolved :=
               (origin, to_prove) :: !(context.cc_unsolved)
         with Fm_solver.Contradiction -> ()

let rec check_expr context expr =
   match expr with
      | Boolean_literal _ -> ()
      | Integer_literal _ -> ()
      | Var_v _ -> ()
      | Comparison(op, lhs, rhs) ->
         check_expr context lhs;
         check_expr context rhs

let rec check_iterm context iterm =
   match iterm with
   | Assignment_term(loc, dest, src, tail) ->
      check_iterm
         {context with
            cc_facts = Comparison(EQ, dest, src)
               :: context.cc_facts}
         tail
   | If_term(loc, condition, true_part, false_part) ->
      check_iterm
         {context with
            cc_facts = condition :: context.cc_facts}
         true_part;
      check_iterm
         {context with
            cc_facts = Negation(condition) :: context.cc_facts}
         false_part
   | Return_term(ret) ->
      begin match ret.ret_subprogram.sym_info with
      Subprogram_sym(info) ->
         List.iter (fun postcondition ->
            prove context
               (From_postconditions(
                  ret.ret_location, ret.ret_subprogram))
               (bind_versions
                  (fun x -> Symbols.Maps.find x ret.ret_versions)
                  postcondition)
         ) info.sub_postconditions
      end
   | Jump_term(loc, target) ->
      List.iter (fun (origin, constr) ->
         prove context origin constr
      ) target.bl_preconditions
   | Call_term(
      {call_candidates =
         [{sym_info=Subprogram_sym(info)} as subprogram]
      } as call, tail)
   ->
      let preconditions = ref info.sub_preconditions in
      let postconditions = ref info.sub_postconditions in
      let invariants = ref [] in
      List.iter2
         (fun ({sym_info=Parameter_sym(mode,_)} as param)
              (arg_in, arg_out) ->
            preconditions := List.map (subst param arg_in) !preconditions;
            postconditions := List.map
               (subst param
                  (match mode, arg_out with
                     | (Const_parameter|In_parameter), None -> arg_in
                     | (Const_parameter|In_parameter), Some arg_out ->
                        invariants := (Comparison(EQ, arg_in, arg_out))
                           :: !invariants;
                        arg_out
                     | (In_out_parameter|Out_parameter), Some arg_out ->
                        arg_out))
               !postconditions
         ) info.sub_parameters call.call_bound_arguments;
      List.iter (fun constr ->
         prove context
            (From_preconditions(call.call_location, subprogram))
            constr
      ) !preconditions;
      check_iterm
         {context with
            cc_facts =
               List.rev_append !postconditions
                  (List.rev_append !invariants context.cc_facts)}
         tail

let constraint_check_blocks blocks =
   let changed = ref true in
   while !changed do
      changed := false;
      List.iter (fun block ->
         let context = {
            cc_unsolved = ref [];
            cc_facts = List.map snd block.bl_preconditions;
         } in
         check_iterm context (unsome block.bl_body);
         prerr_endline (string_of_int (List.length !(context.cc_unsolved))
            ^ " unsolved constraints.")
      ) blocks
   done

