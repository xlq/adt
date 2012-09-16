open Symbols
open Icode
open Misc
open Big_int

type state = {
   mutable ts_calls  : call_info list;
}

type type_error =
   | Type_mismatch of ttype (* found *)
                    * ttype (* expected *)
   | Argument_not_lvalue of symbol (* parameter *)
   | Argument_specified_twice of symbol (* parameter *)
   | Too_many_arguments of symbol (* subprogram *)
   | No_parameter_named of string * symbol (* subprogram *)
   | Missing_argument of symbol (* parameter *)

exception Type_error of Lexing.position * type_error
exception Bail_out

(* This stores changes to the type information that haven't yet
   been added to the "unknown" objects. This information is used
   once an overloaded subprogram has been resolved. *)
type changes = {
   mutable chg_incoming    : (unknown * ttype) list;
   mutable chg_outgoing    : (unknown * ttype) list;
}

(* This stores information about a candidate for an overloaded
   subprogram call. *)
type candidate = {
   can_subprogram          : symbol;
   (* When this candidate is rejected, it is marked with a type error (reason
      for rejection). Before the candidate is rejected, can_rejected is None. *)
   mutable can_rejected    : (Lexing.position * type_error) option;
   (* The parameters from the subprogram are stored as
      (param, None). When an argument is bound to the parameter,
      this is changed to (param, Some (arg_in, ((Some arg_out)|None))). *)
   can_parameters          : (symbol * (expr * expr option) option) array;
   can_changes             : changes;
}

let report_type_error loc = function
   | Type_mismatch(found, expected) ->
      Errors.semantic_error loc
         ("Expected type `"
            ^ string_of_type expected
            ^ "' but found type `"
            ^ string_of_type found
            ^ "'.")

let catch_type_errors (f: 'a -> unit) (x: 'a): unit =
   try f x with Type_error(loc, error) ->
      report_type_error loc error

let commit changes =
   List.iter (fun (unk, t) ->
      unk.unk_incoming <- t :: unk.unk_incoming
   ) changes.chg_incoming;
   List.iter (fun (unk, t) ->
      unk.unk_outgoing <- t :: unk.unk_outgoing
   ) changes.chg_outgoing

let now f =
   let changes = {
      chg_incoming = [];
      chg_outgoing = [];
   } in
   let result = f changes in
   commit changes;
   result

let rec coerce loc t1 t2 changes =
   match t1, t2 with
      | Boolean_type, Boolean_type
      | Integer_type, Integer_type -> ()
      | Unknown_type(unk), t2 ->
         changes.chg_outgoing <- (unk, t2) :: changes.chg_outgoing
      | t1, Unknown_type(unk) ->
         changes.chg_incoming <- (unk, t1) :: changes.chg_incoming
      | _ ->
         raise (Type_error(loc,
            Type_mismatch(t1, t2)))

let rec type_check_expr expected expr changes =
   let got_type loc t =
      match expected with
         | None -> t
         | Some t2 -> coerce loc t t2 changes; t2
   in
   match expr with
      | Boolean_literal(loc,b) ->
         got_type loc Boolean_type
      | Integer_literal(loc,i) ->
         got_type loc Integer_type
      | Var_v(loc,x) ->
         got_type loc x.ver_type
      | Comparison(op, lhs, rhs) ->
         let loc = loc_of_expression lhs in
         let lhs_t = type_check_expr None lhs changes in
         let rhs_t = type_check_expr None rhs changes in
         coerce loc rhs_t lhs_t changes;
         got_type loc Boolean_type

let rec bind_pre_post_condition (post: bool) e =
   let r = bind_pre_post_condition post in
   match e with
      | Boolean_literal _
      | Integer_literal _ -> e
      | Var(loc, param) ->
         begin match param.sym_info with Parameter_sym(mode, t) ->
            let available = match mode with
               | Const_parameter | In_parameter | In_out_parameter -> true
               | Out_parameter when post -> true
               | Out_parameter -> false
            in
            if available then begin
               let param_v = new_version param in
               param_v.ver_type <- t;
               Var_v(loc, param_v)
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
   let changes = {
      chg_incoming = [];
      chg_outgoing = [];
   } in
   List.iter
      (fun constr ->
         catch_type_errors (fun () ->
            ignore
               (type_check_expr
                  (Some Boolean_type)
                  (bind_pre_post_condition false constr)
                  changes))())
      info.sub_preconditions;
   List.iter
      (fun constr ->
         catch_type_errors (fun () ->
            ignore
               (type_check_expr
                  (Some Boolean_type)
                  (bind_pre_post_condition true constr)
                  changes))())
      info.sub_postconditions;
   assert (match changes with {chg_incoming=[]; chg_outgoing=[]} -> true
                            | _ -> false)

let same_mode a b =
   match a, b with
      | Const_parameter, Const_parameter
      | In_parameter, In_parameter
      | Out_parameter, Out_parameter
      | In_out_parameter, In_out_parameter -> true
      | _ -> false

(* XXX: This is very similar to coerce. *)
let conflicting_types t1 t2 =
   match t1, t2 with
      | Boolean_type, Boolean_type
      | Integer_type, Integer_type -> true
      | Boolean_type, _ | _, Boolean_type
      | Integer_type, _ | _, Integer_type -> false

let check_overload
   (competing: symbol list)
   ({sym_declared = Some loc;
     sym_info = Subprogram_sym(info)} as subprogram)
=
   let rec loop = function
      | [], [], _ ->
         (* There are no conflicting declarations. *)
         []
      | [], decls, [] ->
         (* Remove declarations that have more parameters than this one. *)
         List.filter
            (function
               | (_, []) -> true
               | (_, _::_) -> false)
            decls
      | filtered, [], param::params ->
         (* Next parameter. *)
         loop ([], filtered, params)
      | filtered, (decl, [])::decls, param::params ->
         (* This declaration has fewer arguments. Filter it. *)
         loop (filtered, decls, param::params)
      | filtered, (decl, decl_param::decl_params)::decls, param::params ->
         let {sym_info = Parameter_sym(decl_mode, decl_t)} = decl_param in
         let {sym_info = Parameter_sym(mode, t)} = param in
         if (same_mode mode decl_mode)
         && (conflicting_types t decl_t) then
            (* Still conflicting. *)
            loop ((decl, decl_params)::filtered, decls, param::params)
         else
            loop (filtered, decls, param::params)
   in
   match loop
      ([],
       List.map
         (fun ({sym_info = Subprogram_sym(info)} as subprogram) ->
            (subprogram, info.sub_parameters)) competing,
       info.sub_parameters)
   with
      | [] -> ()
      | competing ->
         Errors.semantic_error loc
            ("Declaration of "
               ^ describe_symbol subprogram
               ^ " competes with "
               ^ (match competing with
                  | [_] -> " an earlier declaration."
                  | _::_::_ -> " earlier declarations."));
         List.iter (fun (competing, _) ->
            Errors.semantic_error (unsome competing.sym_declared)
               ("Conflicting declaration of "
                  ^ describe_symbol competing ^ " is here.")
         ) competing

let rec type_check state iterm =
   match iterm with
   | Return_term(ret) ->
      begin match ret.ret_subprogram.sym_info with
      Subprogram_sym(info) ->
         List.iter (fun param ->
            match param.sym_info with
            | Parameter_sym((Out_parameter|In_out_parameter),t) ->
               now
                  (coerce ret.ret_location
                     (Symbols.Maps.find param
                        ret.ret_versions).ver_type
                     t)
            | Parameter_sym((Const_parameter|In_parameter),t) ->
               ()
         ) info.sub_parameters
      end
   | Assignment_term(loc, dest, src, tail) ->
      let src_type = now (type_check_expr None src) in
      let dest_type = now (type_check_expr None dest) in
      now (coerce loc src_type dest_type);
      type_check state tail
   | If_term(loc, condition, true_part, false_part) ->
      ignore (now (type_check_expr (Some Boolean_type) condition));
      type_check state true_part;
      type_check state false_part
   | Jump_term _ ->
      (* There is absolutely nothing to do here, because
         calculate_versions has ensured that the live versions
         at this jump are the same as the jump target's bl_in. *)
      ()
   | Call_term(call, tail) ->
      state.ts_calls <- call :: state.ts_calls;
      type_check state tail

(* Try to resolve a subprogram call.
   Return true on success, false if there's not yet enough
   information to resolve. (Bail_out is propagated if a
   type error is encountered.) *)
let type_check_call call =
   let candidates = List.map
      (function {sym_info=Subprogram_sym(info)} as subprogram ->
         {
            can_subprogram = subprogram;
            can_rejected = None;
            can_parameters = Array.of_list
               (List.map (fun parameter -> (parameter, None))
                info.sub_parameters);
            can_changes = {
               chg_incoming = [];
               chg_outgoing = [];
            };
         }
   ) call.call_candidates in
   let remaining_candidates = ref (List.length candidates) in
   let reject_candidate candidate loc reason =
      candidate.can_rejected <- Some (loc, reason);
      decr remaining_candidates;
      (* Stop if that was the last candidate. *)
      if !remaining_candidates = 0 then begin
         begin match candidates with
         | [x] ->
            assert (x == candidate);
            report_type_error loc reason
         | x::_ ->
            Errors.semantic_error call.call_location
               ("No definition of `" ^ x.can_subprogram.sym_name
                  ^ "' matches these arguments.");
            List.iter (fun candidate ->
               match candidate.can_rejected with Some(loc, reason) ->
                  Errors.semantic_error (unsome candidate.can_subprogram.sym_declared)
                     ("This definition of `" ^ x.can_subprogram.sym_name
                        ^ "' doesn't match because:");
                  report_type_error loc reason
            ) candidates
         end;
         raise Bail_out
      end
   in
   let got_argument candidate i (arg_in, arg_out) =
      match candidate.can_parameters.(i) with
      | ({sym_info=Parameter_sym(param_mode, param_type)} as parameter, None) ->
         (* Mark this parameter as matched. *)
         candidate.can_parameters.(i) <- (parameter, Some(arg_in, arg_out));
         begin try
            let arg_in_t = match param_mode with
               | Out_parameter ->
                  None
               | Const_parameter | In_parameter | In_out_parameter ->
                  Some (type_check_expr (Some param_type) arg_in
                     candidate.can_changes)
            in
            begin match param_mode with
            | Const_parameter ->
               begin match arg_out with
               | Some arg_out ->
                  ignore (
                     type_check_expr
                        (Some (unsome arg_in_t))
                        arg_out candidate.can_changes)
               | None -> ()
               end
            | In_parameter ->
               ()
            | In_out_parameter | Out_parameter ->
               match arg_out with
               | Some arg_out ->
                  coerce (loc_of_expression arg_out)
                     param_type
                     (type_check_expr None arg_out candidate.can_changes)
                     candidate.can_changes
               | None ->
                  reject_candidate candidate
                     (loc_of_expression arg_in)
                     (Argument_not_lvalue parameter)
            end
         with Type_error(loc, error) ->
            reject_candidate candidate loc error
         end
      | (parameter, Some _) ->
         reject_candidate candidate
            (loc_of_expression arg_in)
            (Argument_specified_twice(parameter))
   in
   let positional_args, named_args = call.call_arguments in
   list_iteri (fun i arg ->
      List.iter (fun candidate ->
         match candidate.can_rejected with
            | Some _ -> ()
            | None ->
               if i >= Array.length candidate.can_parameters then begin
                  reject_candidate candidate
                     call.call_location
                     (Too_many_arguments(candidate.can_subprogram))
               end else begin
                  got_argument candidate i arg
               end
      ) candidates;
   ) positional_args;
   List.iter (fun (name, arg) ->
      List.iter (fun candidate ->
         match candidate.can_rejected with
            | Some _ -> ()
            | None ->
               let rec search i =
                  if i >= Array.length candidate.can_parameters then
                     reject_candidate candidate
                        (loc_of_expression (fst arg))
                        (No_parameter_named(name, candidate.can_subprogram))
                  else if (fst candidate.can_parameters.(i)).sym_name = name then
                     got_argument candidate i arg
                  else
                     search (i + 1)
               in search 0
      ) candidates
   ) named_args;
   (* Check that all parameters have arguments. *)
   List.iter (fun candidate ->
      match candidate.can_rejected with
      | Some _ -> ()
      | None ->
         Array.iter (function
            | (_, Some _) -> ()
            | (parameter, None) ->
               reject_candidate candidate
                  call.call_location
                  (Missing_argument(parameter))
         ) candidate.can_parameters
   ) candidates;
   let remaining_candidates = List.filter
      (fun candidate ->
         match candidate.can_rejected with
            | None -> true
            | Some _ -> false)
      candidates
   in
   match remaining_candidates with
      | [candidate] ->
         (* Success! Only one candidate remains. *)
         prerr_endline ("Chose candidate at "
            ^ Errors.string_of_location
               (unsome candidate.can_subprogram.sym_declared));
         commit candidate.can_changes;
         call.call_bound_arguments <-
            Array.fold_right (fun (_, Some x) l -> x::l)
               candidate.can_parameters [];
         call.call_candidates <- [candidate.can_subprogram];
         true
      | [] -> raise (Failure "type_check_call") (* Already raised Bail_out. *)
      | _ ->
         (* Still not resolved. *)
         call.call_candidates <-
            List.map (fun candidate -> candidate.can_subprogram)
               remaining_candidates;
         false

(* TODO: Merge merge_types with coerce? *)
let merge_types t1 t2 =
   try match t1, t2 with
      | Boolean_type, Boolean_type -> Boolean_type
      | Integer_type, Integer_type -> Integer_type
   with (Match_failure _) as e ->
      prerr_endline ("merge_types: failed to merge `"
         ^ string_of_type t1 ^ "' with `"
         ^ string_of_type t2 ^ "'.");
      raise e

let rec propagate_decision unk decided =
   List.iter (function
      | Unknown_type({unk_decided=None} as unk) ->
         unk.unk_decided <- Some decided;
         propagate_decision unk decided
      | _ -> ()
   ) (unk.unk_incoming @ unk.unk_outgoing)

let rec resolve_unknowns_in_type remaining t =
   match t with
   | Boolean_type | Integer_type -> t
   | Unknown_type({unk_decided = Some t}) -> t
   | Unknown_type({unk_decided = None} as unk) ->
      let rec fold result = function
         | [] -> result
         | (Unknown_type {unk_visiting=false} as t)::tail ->
            begin match resolve_unknowns_in_type remaining t with
               | Unknown_type _ -> fold result tail
               | t -> fold result (t::tail)
            end
         | (Unknown_type {unk_visiting=true})::tail ->
            fold result tail
         | t::tail ->
            match result with
               | None -> fold (Some t) tail
               | Some t' -> fold (Some (merge_types t' t)) tail
      in
      unk.unk_visiting <- true;
      unk.unk_decided <-
         fold None (unk.unk_incoming @ unk.unk_outgoing);
      unk.unk_visiting <- false;
      match unk.unk_decided with
         | Some t -> propagate_decision unk t; t
         | None -> remaining := true; t

let rec resolve_unknowns_in_expr remaining e =
   match e with
   | Boolean_literal _ | Integer_literal _ -> ()
   | Var_v(loc, xv) ->
      xv.ver_type <- resolve_unknowns_in_type remaining xv.ver_type
   | Negation(e) -> resolve_unknowns_in_expr remaining e
   | Comparison(_, lhs, rhs) ->
      resolve_unknowns_in_expr remaining lhs;
      resolve_unknowns_in_expr remaining rhs

let rec resolve_unknowns_in_iterm remaining iterm =
   match iterm with
   | Assignment_term(_, dest, _, tail) ->
      resolve_unknowns_in_expr remaining dest;
      resolve_unknowns_in_iterm remaining tail
   | If_term(_, _, true_part, false_part) ->
      resolve_unknowns_in_iterm remaining true_part;
      resolve_unknowns_in_iterm remaining false_part;
   | Return_term _ -> ()
   | Jump_term _ -> ()
   | Call_term(call, tail) ->
      List.iter (fun (_, arg_out) ->
         match arg_out with
            | None -> ()
            | Some e -> resolve_unknowns_in_expr remaining e
      ) (fst call.call_arguments);
      List.iter (fun (_, (_, arg_out)) ->
         match arg_out with
            | None -> ()
            | Some e -> resolve_unknowns_in_expr remaining e
      ) (snd call.call_arguments);
      resolve_unknowns_in_iterm remaining tail

let rec report_unknowns iterm =
   let rec do_iterm = function
      | Assignment_term(_, dest, _, tail) ->
         do_expr dest;
         do_iterm tail
      | If_term(_, _, true_part, false_part) ->
         do_iterm true_part;
         do_iterm false_part
      | Return_term _ -> ()
      | Jump_term _ -> ()
      | Call_term(call, tail) ->
         List.iter (fun (_, arg_out) ->
            match arg_out with
               | None -> ()
               | Some e -> do_expr e) (fst call.call_arguments);
         List.iter (fun (_, (_, arg_out)) ->
            match arg_out with
               | None -> ()
               | Some e -> do_expr e) (snd call.call_arguments);
         do_iterm tail
   and do_expr = function
      | Boolean_literal _ -> ()
      | Integer_literal _ -> ()
      | Var_v(loc, xv) ->
         begin match xv.ver_type with
            | Unknown_type _ ->
               Errors.semantic_error loc
                  ("The type of " ^ describe_symbol xv.ver_symbol
                     ^ " could not be inferred.")
            | _ -> ()
         end
      | Negation(e) -> do_expr e
      | Comparison(_, lhs, rhs) -> do_expr lhs; do_expr rhs
   in do_iterm iterm

let type_check_blocks blocks =
   let state = {ts_calls = []} in
   List.iter (fun block ->
      type_check state (unsome block.bl_body)
   ) blocks;

   let finished = ref false in
   let remaining = ref false in

   while not (!finished) do
      finished := true;
      remaining := false;

      List.iter (fun block ->
         Symbols.Maps.iter (fun _ xv ->
            xv.ver_type <- resolve_unknowns_in_type remaining xv.ver_type
         ) block.bl_in;
         resolve_unknowns_in_iterm remaining (unsome block.bl_body)
      ) blocks;

      state.ts_calls <- begin
         let rec loop result = function
            | [] -> result
            | call::tail ->
               if type_check_call call then begin
                  finished := false;
                  loop result tail
               end else loop (call::result) tail
         in loop [] state.ts_calls
      end
   done;

   begin match state.ts_calls with
      | [] -> ()
      | remaining_calls ->
         List.iter (fun ({call_candidates=first::_} as call) ->
            Errors.semantic_error call.call_location
               ("Call of overloaded subprogram `"
                  ^ first.sym_name ^ "' is ambiguous.");
            List.iter (fun subprogram ->
               Errors.semantic_error (unsome subprogram.sym_declared)
                  ("This definition of `" ^ first.sym_name
                     ^ "' matches.")
            ) call.call_candidates
         ) remaining_calls
   end;

   if !remaining then begin
      prerr_endline "Some unknowns remain!";
      (* Report types that were not inferred. *)
      List.iter (fun block ->
         report_unknowns (unsome block.bl_body)
      ) blocks
   end else begin
      prerr_endline "No unknowns remain. Good."
   end;

   prerr_endline "";
   prerr_endline "Dumping blocks with computed types...";
   let f = Formatting.new_formatter () in
   dump_blocks f blocks;
   prerr_endline (Formatting.get_fmt_str f)
