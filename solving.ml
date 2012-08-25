open Symbols
open Big_int

type factor = symbol * version

type term =
   | Const of big_int
   | Product of big_int * factor

(* An inequality is of the form ax + by + ... + cz + m >= 0 *)
type inequality = term list

let rec subst (x_sym, x_version) replacement m =
   let r = subst (x_sym, x_version) replacement in
   match m with
      | Boolean_literal _ -> m
      | Integer_literal _ -> m
      | Var_version(x,v) when (x == x_sym) && (v = x_version) -> replacement
      | Var_version _ -> m
      | Equal(i,j) -> Equal(r i, r j)
      | For_all(x,v,n) when (x == x_sym) && (v = x_version) -> m
      | For_all(x,v,n) -> For_all(x,v,r n)
      | Conjunction p -> Conjunction (List.map r p)
      | Implication(p,q) -> Implication(r p, r q)

let convert (constr: expr): inequality list =
   let rec negative (pos, neg) = function
      | For_all(_,_,e) -> negative (pos, neg) e
      | Conjunction p ->
         List.fold_left (fun ax p -> negative ax p) (pos, neg) p
      | Implication(p,q) ->
         negative (positive (pos, neg) p) q
      | Boolean_literal(true) ->
         (pos, neg)
      | Var_version(x,v) ->
         (* Must be boolean *)
         (pos, (Var_version(x,v))::neg)

   and positive (pos, neg) = function
      | Equal(i,j) ->
         (Equal(i,j)::pos, neg)
      | Conjunction p ->
         List.fold_left (fun ax p -> positive ax p) (pos, neg) p
   in

   let pos, neg = negative ([], []) constr in
   List.iter (fun pos ->
      prerr_endline ("        " ^ string_of_expr pos)) pos;
   List.iter (fun neg ->
      prerr_endline ("    not " ^ string_of_expr neg)) neg;
   []

let solve
   (important_vars: version Symbols.Maps.t)
   (constr: expr)
=
   ignore (convert constr)
