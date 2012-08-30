open Symbols
open Big_int

exception Non_linear_constraint
exception Contradiction

type term =
   | Lin_const of big_int
   | Lin_mul of big_int * symbol_v

type inequality =
   (* Natural[a;b;c] is a+b+c >= 0
      Invariant: Only one term is Lin_const.
      Invariant: Each variable occurs at most once.
      Natural[] is 0 >= 0. *)
   | Natural of term list

let string_of_term = function
   | Lin_const(i) -> string_of_big_int i
   | Lin_mul(i,x) ->
      if eq_big_int i unit_big_int then
         full_name_v x
      else if eq_big_int i (minus_big_int unit_big_int) then
         "-" ^ full_name_v x
      else
         string_of_big_int i
            ^ "*" ^ full_name_v x

let string_of_inequality = function
   | Natural [] -> "0 >= 0"
   | Natural(terms) ->
      String.concat " + " (List.map string_of_term terms)
         ^ " >= 0"

(* Add a term to a list of terms (preserving the invariants for Natural). *)
let add_term (terms: term list): term -> term list =
function
   | Lin_const(i) ->
      let rec loop result = function
         | [] ->
            if eq_big_int i zero_big_int then
               result
            else
               Lin_const(i) :: result
         | Lin_const(j)::tail ->
            let i_add_j = add_big_int i j in
            if eq_big_int i_add_j zero_big_int then
               result @ tail
            else
               result @ Lin_const(i_add_j) :: tail
         | thing::tail -> loop (thing::result) tail
      in loop [] terms
   | Lin_mul(i,x) ->
      let rec loop result = function
         | [] -> Lin_mul(i,x) :: result
         | Lin_mul(j,x')::tail when x == x' ->
            let i_add_j = add_big_int i j in
            if eq_big_int i_add_j zero_big_int then
               result @ tail
            else
               result @ Lin_mul(i_add_j, x) :: tail
         | thing::tail -> loop (thing::result) tail
      in loop [] terms

let add_const i terms =
   add_term terms (Lin_const(big_int_of_int i))

(* Add a list of terms to another. *)
let add_terms terms1 terms2 =
   (* XXX: Quadratic in number of terms! *)
   List.fold_left add_term terms1 terms2

(* Subtract a term from zero. *)
let negate_term = function
   | Lin_const(i) -> Lin_const(minus_big_int i)
   | Lin_mul(i,x) -> Lin_mul(minus_big_int i, x)

(* Subtract a list of terms from another. *)
let subtract_terms terms1 terms2 =
   (* XXX: Quadratic in number of terms! *)
   List.fold_left (fun terms1 term2 ->
      add_term terms1 (negate_term term2)) terms1 terms2

(* Add to "terms" a linear version of the given integer expression.
   Adds nothing if the given expression cannot be linearised. *)
let linearise_expr (terms: term list): expr -> term list =
function
   | Integer_literal(i) ->
      add_term terms (Lin_const(i))
   | Var_v(x) ->
      add_term terms (Lin_mul(unit_big_int, x))
   | Negation _ | Comparison _ | Boolean_literal _ ->
      (* Irrelevant. *)
      terms

(* Add to "inequalities" a linear version of the given comparison expression.
   Adds nothing if the given expression cannot be linearised. *)
let linearise: expr -> inequality list =
function
   | Comparison(op, lhs, rhs) ->
      let lhs' = linearise_expr [] lhs in
      let rhs' = linearise_expr [] rhs in
      begin match op with
         | EQ ->
            [Natural(subtract_terms lhs' rhs');
             Natural(subtract_terms rhs' lhs')]
         | LT ->
            [Natural(add_const (-1) (subtract_terms rhs' lhs'))]
         | LE ->
            [Natural(subtract_terms rhs' lhs')]
      end
   | _ -> raise Non_linear_constraint

(* Negate an inequality. *)
let negate (Natural(terms)) =
   (*  not (x >= 0)
       ==>   x < 0
       ==>  -x > 0
       ==>  -x-1 >= 0  *)
   Natural(add_const (-1) (List.map negate_term terms))

(* Return the coefficient of x in the given inequality.
   Relies on the Natural invariants. *)
let coefficient_of x (Natural(terms)) =
   let rec search = function
      | [] -> zero_big_int
      | (Lin_const _)::tail -> search tail
      | (Lin_mul(i,x'))::_ when x == x' -> i
      | (Lin_mul _)::tail -> search tail
   in search terms

(* Does x occur in these constraints? *)
let occurs x constrs =
   not (eq_big_int (coefficient_of x constrs) zero_big_int)

(* Return a list of all free variables in a set of inequalities. *)
let free_ineqs ineqs =
   let in_term result = function
      | Lin_const _ -> result
      | Lin_mul(i,x) -> x::result
   in
   let in_ineq result (Natural(terms)) =
      List.fold_left in_term result terms
   in
   List.fold_left in_ineq [] ineqs

(* Discard a constraint with no variables. *)
let elim_const = function
   | Natural [] ->
      (* 0 >= 0 *)
      None
   | Natural [Lin_const i] ->
      begin if lt_big_int i zero_big_int then
         (* Contradiction: i >= 0 and i < 0 *)
         raise Contradiction
      end;
      None
   | x -> Some x

(*****  Multiply a sum by a constant  *****
 *
 *  ax + by + ... + cz + m >= 0
 *      is equivalent to
 *  anx + bny + ... + cnz + mn >= 0
 *      as long as n > 0
 *)
let multiply_term coef = function
    | Lin_const i -> Lin_const (mult_big_int i coef)
    | Lin_mul(i,x) -> Lin_mul(mult_big_int i coef, x)

let multiply_sum coef terms =
    assert (gt_big_int coef zero_big_int);
    List.map (multiply_term coef) terms

(* For ax + by + ... + cz + dv + ev + m >= 0
   return (d+e), ax + by + ... + cz + m >= 0 *)
let extract_coefficient var m =
   let rec search coef m' = function
       | [] -> (coef, m')
       | (Lin_mul(i,x))::l when x == var ->
           search (add_big_int i coef) m' l
       | x::l ->
           search coef (x::m') l
   in search zero_big_int [] m

(* Multiply and add two inequalities in order to eliminate x. *)
let combine_inequalities x (Natural a) (Natural b) =
    (*  ax + ... >= 0     bx + ... >= 0     (a > 0, b < 0)
           * -b                * a
        -abx + ... >= 0   abx + ... >= 0 *)

    let coef_x_in_a, a' = extract_coefficient x a in
    let coef_x_in_b, b' = extract_coefficient x b in
    assert (gt_big_int coef_x_in_a zero_big_int);
    assert (lt_big_int coef_x_in_b zero_big_int);
    (* TODO: Use GCD to avoid absurdly large numbers? *)
    let a'' = multiply_sum (minus_big_int coef_x_in_b) (a') in
    let b'' = multiply_sum (              coef_x_in_a) (b') in
    (* After scaling, the coefficients of x in the two inequalities are equal
       and opposite, so adding the two inequalities eliminates x.
       Note that x was extracted by extract_coefficient, so is
       not present in a'' or b''. *)
    Natural(add_terms a'' b'')

let dump s ineq =
   prerr_endline s;
   List.iter (fun ineq ->
      prerr_endline ("    " ^ string_of_inequality ineq)) ineq

(* Fourier-Motzkin variable elimination. *)
let eliminate x inequalities =
   let ab, phi = List.partition (occurs x) inequalities in
   let a, b =
      List.partition
         (fun constr -> gt_big_int (coefficient_of x constr) zero_big_int)
         ab
   in
   match a, b with
   | [], _ | _, [] -> None
   | _ ->
      let result = ref phi in
      List.iter (fun a ->
         List.iter (fun b ->
            match elim_const (combine_inequalities x a b) with
               | Some constr -> result := constr :: !result
               | None -> ()
         ) b
      ) a;
      dump ("Eliminated " ^ full_name_v x
         ^ " to get:") !result;
      Some !result

let solve inequalities =
   dump "Solving linear inequalities:" inequalities;
   let system = ref inequalities in
   let vars = free_ineqs !system in
   List.iter (fun x ->
      match eliminate x !system with
         | None -> ()
         | Some system' -> system := system'
   ) vars;
   dump "Result:" !system
