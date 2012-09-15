open Misc
open Formatting
open Big_int
open Symbols

let next_block_id = ref 0
let new_block_id () =
   incr next_block_id;
   !next_block_id

type loc = Parse_tree.loc

type constraint_origin =
   | From_postconditions of Lexing.position * symbol
   | From_preconditions of Lexing.position * symbol
   | From_static_assertion of Lexing.position

type iterm =
   | Assignment_term of loc * expr * expr * iterm
   | If_term of loc * expr * iterm * iterm
   | Return_term of return_info
   | Jump_term of loc * block
   | Call_term of call_info * iterm
   | Inspect_type_term of loc * symbol * iterm
   | Static_assert_term of loc * expr * iterm

and return_info =
   {
      ret_location      : loc;
      (* Subprogram being returned from. *)
      ret_subprogram    : symbol;
      (* Versions of variables to bind to the out parameters
         of the subprogram. This is empty until after
         calculate_free_names. *)
      ret_versions      : symbol_v Symbols.Maps.t;
   }

and call_info =
   {
      call_location   : loc;
      call_candidates : symbol list;
      mutable call_arguments
                      : (expr * expr option) list
                      * (string * (expr * expr option)) list;
      mutable call_bound_arguments
                      : expr list;
   }

and block =
   {
      bl_id                   : int;
      mutable bl_body         : iterm option;
      mutable bl_in           : symbol_v Symbols.Maps.t;
      mutable bl_preconditions: (constraint_origin * expr) list;
   }

let rec dump_term (f: formatter) = function
   | Return_term(_) -> puts f "return"
   | Assignment_term(_,x,m,tail) ->
      puts f (string_of_lvalue x ^ " := "
         ^ string_of_expr m ^ ";");
      break f;
      dump_term f tail
   | If_term(_,cond,a,b) ->
      puts f ("if " ^ string_of_expr cond ^ " then");
      break f; indent f; dump_term f a;
      break f; undent f; puts f "else"; break f; indent f;
      dump_term f b; undent f;
   | Jump_term(_,bl) ->
      puts f ("tail block" ^ string_of_int bl.bl_id)
   | Call_term(call, tail) ->
      let positional_args, named_args = call.call_arguments in
      puts f ("call "
         ^ (List.hd call.call_candidates).sym_name
         ^ " (" ^ String.concat ", "
            (List.map
               (fun (arg_in, arg_out) ->
                  "in " ^ string_of_expr arg_in
                     ^ match arg_out with
                        | Some arg_out -> " out " ^ string_of_lvalue arg_out
                        | None -> "")
               positional_args
             @ List.map
               (fun (name, (arg_in, arg_out)) ->
                  name ^ " => in " ^ string_of_expr arg_in
                     ^ match arg_out with
                        | Some arg_out -> " out " ^ string_of_lvalue arg_out
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
            Symbols.Maps.iter (fun _ x ->
               puts f ("| " ^ full_name_v x
                  ^ ": " ^ string_of_type x.ver_type);
               break f
            ) bl.bl_in
         end;
         List.iter (fun (_, p) ->
            puts f ("| "
               ^ string_of_expr p);
            break f
         ) bl.bl_preconditions;
         indent f;
         dump_term f e;
         undent f; break f

let dump_blocks (f: formatter) (blocks: block list) =
   List.iter (dump_block f) blocks

let loc_of_constraint_origin = function
   | From_postconditions(loc, _)
   | From_preconditions(loc, _)
   | From_static_assertion(loc) -> loc

let describe_constraint_origin = function
   | From_postconditions(_, sub) ->
      "a post-condition of " ^ describe_symbol sub
   | From_preconditions(_, sub) ->
      "a pre-condition of calling " ^ describe_symbol sub
   | From_static_assertion(_) ->
      "a static assertion"

let all_variables (blocks: block list): unit Symbols.Maps.t =
   let vars = ref Symbols.Maps.empty in
   let rec search_expr = function
      | Boolean_literal _ -> ()
      | Integer_literal _ -> ()
      | Var(loc, x) -> vars := Symbols.Maps.add x () !vars
      | Negation(e) -> search_expr e
      | Comparison(op, lhs, rhs) ->
         search_expr lhs; search_expr rhs
   in
   let rec search_iterm = function
      | Assignment_term(loc, dest, src, tail) ->
         search_expr dest;
         search_expr src;
         search_iterm tail
      | If_term(loc, cond, true_part, false_part) ->
         search_expr cond;
         search_iterm true_part;
         search_iterm false_part
      | Return_term(ret) -> ()
      | Jump_term _ -> ()
      | Call_term(call, tail) ->
         let positional, named = call.call_arguments in
         List.iter (fun (arg_in, _) -> search_expr arg_in) positional;
         List.iter (fun (_, (arg_in, _)) -> search_expr arg_in) named;
         search_iterm tail
      | Inspect_type_term(loc, x, tail) ->
         vars := Symbols.Maps.add x () !vars;
         search_iterm tail
   in
   List.iter (fun block ->
      search_iterm (unsome block.bl_body)) blocks;
   !vars

let rec last_version xv =
   match xv.ver_next with
      | None -> xv
      | Some xv' -> last_version xv'

let merge_versions xv xv' =
   let xv = last_version xv in
   let xv' = last_version xv' in
   if xv != xv' then xv.ver_next <- Some xv'

let calculate_versions (blocks: block list): unit =

   (* Create a new version for every free variable of every block,
      then link versions together across jumps. *)

   let vars = all_variables blocks in
   List.iter (fun block ->
      block.bl_in <- Symbols.Maps.fold
         (fun x () bl_in ->
            if Symbols.Maps.mem x bl_in then bl_in
            else Symbols.Maps.add x (new_version x) bl_in
         ) vars block.bl_in
   ) blocks;

   let rec bind_expr context = function
      | (Boolean_literal _) as e -> e
      | (Integer_literal _) as e -> e
      | Var(loc, x) -> Var_v(loc, Symbols.Maps.find x context)
      | Negation(e) -> Negation(bind_expr context e)
      | Comparison(op, lhs, rhs) ->
         Comparison(op, bind_expr context lhs, bind_expr context rhs)
   in
   let rec bind_lvalue context = function
      | Var(loc, x) ->
         let xv = new_version x in
         (Symbols.Maps.add x xv context,
          Var_v(loc, xv))
   in
   let rec bind_iterm context = function
      | Assignment_term(loc, dest, src, tail) ->
         let src = bind_expr context src in
         let context, dest = bind_lvalue context dest in
         let tail = bind_iterm context tail in
         Assignment_term(loc, dest, src, tail)
      | If_term(loc, cond, true_part, false_part) ->
         If_term(loc,
            bind_expr context cond,
            bind_iterm context true_part,
            bind_iterm context false_part)
      | Return_term(ret) ->
         begin match ret.ret_subprogram.sym_info with Subprogram_sym(info) ->
            Return_term({ret with ret_versions =
               List.fold_left (fun ret_versions parameter ->
                  match parameter.sym_info with Parameter_sym(mode, t) ->
                     match mode with
                        | In_out_parameter | Out_parameter ->
                           Symbols.Maps.add
                              parameter
                              (Symbols.Maps.find parameter context)
                              ret_versions
                        | Const_parameter | In_parameter ->
                           ret_versions
               ) Symbols.Maps.empty info.sub_parameters
            })
         end
      | (Jump_term(loc, target)) as e ->
         Symbols.Maps.iter (fun x xv ->
            let xv' = Symbols.Maps.find x target.bl_in in
            merge_versions xv xv'
         ) context;
         e
      | Call_term(call, tail) ->
         let positional, named = call.call_arguments in
         let input_context = context in
         let output_context = ref context in
         let do_args (arg_in, arg_out) =
            let arg_in = bind_expr input_context arg_in in
            let arg_out =
               match arg_out with
                  | None -> None
                  | Some arg_out ->
                     let context', arg_out' = bind_lvalue !output_context arg_out in
                     output_context := context';
                     Some arg_out'
            in (arg_in, arg_out)
         in
         let positional = List.map do_args positional in
         let named = List.map (fun (name, args) ->
            (name, do_args args)) named in
         let tail = bind_iterm !output_context tail in
         Call_term({call with
            call_arguments = (positional, named)}, tail)
      | Inspect_type_term(loc, x, tail) ->
         Inspect_type_term(loc, x, bind_iterm context tail)
      | Static_assert_term(loc, expr, tail) ->
         Static_assert_term(loc,
            bind_expr context expr,
            bind_iterm context tail)
   in

   List.iter (fun block ->
      block.bl_body <- Some
         (bind_iterm block.bl_in (unsome block.bl_body))
   ) blocks;

   let rec finish_expr = function
      | (Boolean_literal _) as e -> e
      | (Integer_literal _) as e -> e
      | Var_v(loc, xv) -> Var_v(loc, last_version xv)
      | Negation(e) -> Negation(finish_expr e)
      | Comparison(op, lhs, rhs) ->
         Comparison(op, finish_expr lhs, finish_expr rhs)
   in
   let rec finish_iterm = function
      | Assignment_term(loc, dest, src, tail) ->
         Assignment_term(loc, finish_expr dest, finish_expr src,
            finish_iterm tail)
      | If_term(loc, cond, true_part, false_part) ->
         If_term(loc, finish_expr cond,
            finish_iterm true_part, finish_iterm false_part)
      | Return_term(ret) ->
         Return_term({ret with
            ret_versions = Symbols.Maps.map last_version
               ret.ret_versions})
      | (Jump_term _) as e -> e
      | Call_term(call, tail) ->
         let positional, named = call.call_arguments in
         let do_args (arg_in, arg_out) =
            let arg_in = finish_expr arg_in in
            let arg_out = match arg_out with
               | None -> None
               | Some arg_out ->
                  Some (finish_expr arg_out)
            in
            (arg_in, arg_out)
         in
         let positional = List.map do_args positional in
         let named = List.map (fun (name, args) -> (name, do_args args)) named in
         Call_term({call with call_arguments = (positional, named)},
            finish_iterm tail)
      | Inspect_type_term(loc, x, tail) ->
         Inspect_type_term(loc, x, finish_iterm tail)
      | Static_assert_term(loc, e, tail) ->
         Static_assert_term(loc, finish_expr e, finish_iterm tail)
   in

   List.iter (fun block ->
      block.bl_in <- Symbols.Maps.map last_version block.bl_in;
      block.bl_body <- Some
         (finish_iterm (unsome block.bl_body))
   ) blocks
