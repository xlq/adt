open Misc
open Formatting
open Big_int
open Symbols

let next_block_id = ref 0
let new_block_id () =
   incr next_block_id;
   !next_block_id

type loc = Parse_tree.loc

type liveness_origin =
   | Used_variable of Lexing.position
   | From_parameters

type iterm =
   | Null_term of loc
   | Assignment_term of loc * expr * expr * iterm
   | If_term of loc * expr * iterm * iterm
   | Jump_term of jump_info
   | Call_term of call_info * iterm
   | Inspect_type_term of loc * symbol * iterm
   | Static_assert_term of loc * expr * iterm

and jump_info =
   {
      jmp_location      : loc;
      jmp_target        : block;
      jmp_versions      : symbol_v Symbols.Maps.t;
   }

and call_info =
   {
      call_location   : loc;
      call_target     : symbol;
      call_arguments  : (expr * expr option) list
                      * (string * (expr * expr option)) list;
      mutable call_bound_arguments
                      : expr list;
   }

and block =
   {
      bl_id                   : int;
      bl_statement            : Parse_tree.statement;
      mutable bl_body         : iterm option;
      mutable bl_in           : (liveness_origin * symbol_v) Symbols.Maps.t;
      mutable bl_preconditions: expr list;
   }

let rec dump_term (f: formatter) = function
   | Null_term(_) -> puts f "null"
   | Assignment_term(_,x,m,tail) ->
      puts f (string_of_expr x ^ " := "
         ^ string_of_expr m ^ ";");
      break f;
      dump_term f tail
   | If_term(_,cond,a,b) ->
      puts f ("if " ^ string_of_expr cond ^ " then");
      break f; indent f; dump_term f a;
      break f; undent f; puts f "else"; break f; indent f;
      dump_term f b; undent f;
   | Jump_term {jmp_target=bl} ->
      puts f ("tail block" ^ string_of_int bl.bl_id)
   | Call_term(call, tail) ->
      let positional_args, named_args = call.call_arguments in
      puts f ("call "
         ^ full_name call.call_target
         ^ " (" ^ String.concat ", "
            (List.map
               (fun (arg_in, arg_out) ->
                  "in " ^ string_of_expr arg_in
                     ^ match arg_out with
                        | Some arg_out -> " out " ^ string_of_expr arg_out
                        | None -> "")
               positional_args
             @ List.map
               (fun (name, (arg_in, arg_out)) ->
                  name ^ " => in " ^ string_of_expr arg_in
                     ^ match arg_out with
                        | Some arg_out -> " out " ^ string_of_expr arg_out
                        | None -> "")
               named_args)
         ^ ");");
      break f;
      dump_term f tail
   | Inspect_type_term(_,_,tail) ->
      dump_term f tail
   | Static_assert_term(_,expr,tail) ->
      puts f ("Static_Assert " ^ string_of_expr expr ^ ";");
      break f;
      dump_term f tail

let dump_block (f: formatter) (bl: block) =
   match bl.bl_body with
      | None -> ()
      | Some e ->
         puts f ("block" ^ string_of_int bl.bl_id ^ ":");
         break f;
         if not (Symbols.Maps.is_empty bl.bl_in) then begin
            Symbols.Maps.iter (fun _ (_, x) ->
               puts f ("| "
                  ^ full_name_v x
                  ^ ": " ^ string_of_type (unsome x.ver_type));
               break f
            ) bl.bl_in
         end;
         List.iter (fun p ->
            puts f ("| "
               ^ string_of_expr p);
            break f
         ) bl.bl_preconditions;
         indent f;
         dump_term f e;
         undent f; break f

let dump_blocks (f: formatter) (blocks: block list) =
   List.iter (dump_block f) blocks

let map_minus_set
   (a: 'a Symbols.Maps.t)
   (b: Symbols.Sets.t): 'a Symbols.Maps.t
=
   Symbols.Sets.fold Symbols.Maps.remove b a

let equal_keys a b =
   let rec compare = function
      | [], [] -> true
      | [], _ | _, [] -> false
      | (x,_)::l, (x',_)::l' when x == x' -> compare (l, l')
      | _::_, _::_ -> false
   in compare (Symbols.Maps.bindings a, Symbols.Maps.bindings b)

let map_union_map assert_same =
   Symbols.Maps.merge
      (fun _ a b ->
         match a, b with
            | None, None -> None
            | Some a, None -> Some a
            | None, Some b -> Some b
            | Some a, Some b ->
               assert_same a b;
               Some a
      )

let rec bind_versions_lvalue context e =
   match e with
      | Var_v(_,x) -> Symbols.Maps.add x.ver_symbol x context

let rec bind_versions_expr context e =
   match e with
      | Boolean_literal _
      | Integer_literal _ -> e
      | Var(loc, x) -> Var_v(loc, Symbols.Maps.find x context)
      | Var_v(loc, x) -> raise (Failure "bind_versions_expr")
      | Negation(e) -> Negation(bind_versions_expr context e)
      | Comparison(op, lhs, rhs) ->
         Comparison(op,
                    bind_versions_expr context lhs,
                    bind_versions_expr context rhs)

let rec bind_versions context iterm =
   match iterm with
      | Null_term _ -> iterm
      | Assignment_term(loc, dest, src, tail) ->
         let src = bind_versions_expr context src in
         let context = bind_versions_lvalue context dest in
         Assignment_term(loc, dest, src, bind_versions context tail)
      | If_term(loc, cond, true_part, false_part) ->
         If_term(loc, bind_versions_expr context cond,
                      bind_versions context true_part,
                      bind_versions context false_part)
      | Jump_term(jmp) ->
         Jump_term {jmp with
            jmp_versions = Symbols.Maps.mapi
               (fun x _ -> Symbols.Maps.find x context)
               jmp.jmp_target.bl_in}
      | Call_term(call, tail) ->
         assert (match call.call_bound_arguments with [] -> true | _ -> false);
         let positional_args, named_args = call.call_arguments in
         (* Bind inputs. *)
         let positional_args =
            List.map
               (fun (arg_in, arg_out) ->
                  (bind_versions_expr context arg_in, arg_out))
               positional_args
         in
         let named_args =
            List.map
               (fun (name, (arg_in, arg_out)) ->
                  (name, (bind_versions_expr context arg_in, arg_out)))
               named_args
         in
         (* Add outputs to context. *)
         let context =
            List.fold_left
               (fun context (arg_in, arg_out) ->
                  match arg_out with
                     | Some arg_out -> bind_versions_lvalue context arg_out
                     | None -> context)
               context positional_args
         in
         let context =
            List.fold_left
               (fun context (name, (arg_in, arg_out)) ->
                  match arg_out with
                     | Some arg_out -> bind_versions_lvalue context arg_out
                     | None -> context)
               context named_args
         in
         Call_term(
            {call with call_arguments = (positional_args, named_args)},
            bind_versions context tail)
      | Inspect_type_term(loc, x, tail) ->
         Inspect_type_term(loc, x, bind_versions context tail)
      | Static_assert_term(loc, m, tail) ->
         Static_assert_term(loc, bind_versions_expr context m, bind_versions context tail)

let calculate_free_names (blocks: block list): unit =
   (* First pass: collect free and bound names. *)
   let (jumps: (block * jump_info * Symbols.Sets.t) list ref) = ref [] in
   List.iter (fun block ->
      let rec search
         (free: (liveness_origin * symbol_v) Symbols.Maps.t)
         (bound: Symbols.Sets.t):
         iterm -> (liveness_origin * symbol_v) Symbols.Maps.t
      = function
         | Null_term _ | Inspect_type_term _ -> free
         | Assignment_term(_,dest,src,p) ->
            let free, bound = esearch_lvalue free bound dest in
            search (esearch free bound src) bound p
         | If_term(_,cond,truep,falsep) ->
            search
               (search
                  (esearch free bound cond)
                  bound truep)
               bound falsep
         | Jump_term jump ->
            jumps := (block, jump, bound) :: !jumps;
            free
         | Call_term(call, tail) ->
            let (pos_args, named_args) = call.call_arguments in
            (* Add inputs to free variables. *)
            let free =
               List.fold_left
                  (fun free (arg_in, arg_out) ->
                     esearch free bound arg_in)
                  free pos_args
            in
            let free =
               List.fold_left
                  (fun free (name, (arg_in, arg_out)) ->
                     esearch free bound arg_in)
                  free named_args
            in
            (* Add changed variables in outputs to bound. *)
            let free, bound =
               List.fold_left
                  (fun (free, bound) (arg_in, arg_out) ->
                     match arg_out with
                        | Some arg_out -> esearch_lvalue free bound arg_out
                        | None -> (free, bound))
                  (free, bound) pos_args
            in
            let free, bound =
               List.fold_left
                  (fun (free, bound) (name, (arg_in, arg_out)) ->
                     match arg_out with
                        | Some arg_out -> esearch_lvalue free bound arg_out
                        | None -> (free, bound))
                  (free, bound) named_args
            in
            search free bound tail
         | Static_assert_term(loc, expr, tail) ->
            search
               (esearch free bound expr)
               bound tail
      and esearch
         (free: (liveness_origin * symbol_v) Symbols.Maps.t)
         (bound: Symbols.Sets.t):
         expr -> (liveness_origin * symbol_v) Symbols.Maps.t
      = function
         | Boolean_literal _ | Integer_literal _ -> free
         | Var(loc, x) ->
            if Symbols.Sets.mem x bound then begin
               (* x was bound further up. *)
               free
            end else begin
               (* x is not bound - it was live at the start of this block. *)
               Symbols.Maps.add x (Used_variable loc, new_version x) free
            end
         | Comparison(op, lhs, rhs) ->
            esearch (esearch free bound lhs) bound rhs
      and esearch_lvalue
         (free: (liveness_origin * symbol_v) Symbols.Maps.t)
         (bound: Symbols.Sets.t):
         expr -> ((liveness_origin * symbol_v) Symbols.Maps.t) * Symbols.Sets.t
      = function
         | Var_v(loc, x) ->
            free, Symbols.Sets.add x.ver_symbol bound
      in
      block.bl_in <- search Symbols.Maps.empty Symbols.Sets.empty
         (unsome block.bl_body)
   ) blocks;

   (* Second pass: extend free name sets of blocks. *)
   let changed = ref true in
   while (!changed) = true do
      changed := false;
      List.iter (fun (block, jump, bound) ->
         let jump_free =
            map_minus_set
               jump.jmp_target.bl_in   (* variables that are free in the jump target *)
               bound                   (* and are not bound above the jump in its block *)
         in
         let new_free =
            map_union_map
               (fun (_, a) (_, b) -> assert (a == b))
               block.bl_in
               jump_free
         in
         if not (equal_keys block.bl_in new_free) then begin
            block.bl_in <- new_free;
            changed := true
         end
      ) !jumps
   done;

   (* Bind variables to versions. *)
   List.iter (fun block ->
      let context = Symbols.Maps.map snd block.bl_in in
      block.bl_body <- Some (bind_versions context (unsome block.bl_body))
   ) blocks
