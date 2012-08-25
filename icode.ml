open Misc
open Formatting
open Big_int
open Symbols

let next_block_id = ref 0
let new_block_id () =
   incr next_block_id;
   !next_block_id

type loc = Parse_tree.loc

type iterm =
   | Null_term of loc
   | Assignment_term of loc * symbol * expr * iterm
   | If_term of loc * expr * iterm * iterm
   | Jump_term of jump_info
   | Inspect_type_term of loc * symbol * iterm
   | Static_assert_term of loc * expr * iterm

and jump_info =
   {
      jmp_location      : loc;
      jmp_target        : block;
      mutable jmp_bound : Symbols.Sets.t;
   }

and block =
   {
      bl_id                   : int;
      bl_statement            : Parse_tree.statement;
      mutable bl_body         : iterm option;
      mutable bl_free         : Symbols.Sets.t;
      mutable bl_preconditions: expr list;
      mutable bl_in           : (ttype * version) Symbols.Maps.t;
   }

let rec dump_term (f: formatter) = function
   | Null_term(_) -> puts f "null"
   | Assignment_term(_,x,m,tail) ->
      puts f (full_name x ^ " := "
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
            Symbols.Maps.iter (fun x (t, x_ver) ->
               puts f ("| "
                  ^ full_name_with_version x x_ver
                  ^ ": " ^ string_of_type t);
               break f
            ) bl.bl_in
         end else if not (Symbols.Sets.is_empty bl.bl_free) then begin
            Symbols.Sets.iter (fun x ->
               puts f ("| " ^ full_name x ^ ": <unknown>");
               break f
            ) bl.bl_free
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

let calculate_free_names (blocks: block list): unit =
   (* First pass: collect free and bound names. *)
   let (jumps: (block * jump_info) list ref) = ref [] in
   List.iter (fun block ->
      let rec search (free: Symbols.Sets.t) (bound: Symbols.Sets.t):
         iterm -> Symbols.Sets.t
      = function
         | Null_term _ | Inspect_type_term _ -> free
         | Assignment_term(_,x,m,p) ->
            search
               (esearch free bound m)
               (Symbols.Sets.add x bound)
               p
         | If_term(_,cond,truep,falsep) ->
            search
               (search
                  (esearch free bound cond)
                  bound truep)
               bound falsep
         | Jump_term jump ->
            jump.jmp_bound <- bound;
            jumps := (block, jump) :: !jumps;
            free
         | Static_assert_term(loc, expr, tail) ->
            search
               (esearch free bound expr)
               bound tail
      and esearch (free: Symbols.Sets.t) (bound: Symbols.Sets.t):
         expr -> Symbols.Sets.t
      = function
         | Boolean_literal _ | Integer_literal _ -> free
         | Var x ->
            if Symbols.Sets.mem x bound then begin
               (* x was bound further up. *)
               free
            end else begin
               (* x is not bound - it was live at the start of this block. *)
               Symbols.Sets.add x free
            end
         | Operation(op, lhs, rhs) ->
            esearch (esearch free bound lhs) bound rhs
      in
      block.bl_free <- search Symbols.Sets.empty Symbols.Sets.empty
         (unsome block.bl_body)
   ) blocks;

   (* Second pass: extend free name sets of blocks. *)
   let changed = ref true in
   while (!changed) = true do
      changed := false;
      List.iter (fun (block, jump) ->
         let jump_free =
            Symbols.Sets.diff
               jump.jmp_target.bl_free (* variables that are free in the jump target *)
               jump.jmp_bound          (* and are not bound above the jump in its block *)
         in
         let new_free =
            Symbols.Sets.union
               block.bl_free
               jump_free
         in
         if not (Symbols.Sets.equal block.bl_free new_free) then begin
            block.bl_free <- new_free;
            changed := true
         end
      ) !jumps
   done;

   (* Clean up. *)
   List.iter (fun (_, jump) -> jump.jmp_bound <- Symbols.Sets.empty) !jumps
