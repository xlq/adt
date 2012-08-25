(* Fourier-Motzkin constraint solver. *)

exception Non_linear_constraint
exception Contradiction

type inequality

val string_of_inequality : inequality -> string

(* Make an inequality out of the given expression.
   Propagates Non_linear_constraint if the expression
   doesn't represent a linear constraint. *)
val linearise : Symbols.expr -> inequality list

(* Negate an inequality, i.e. e is true iff (negate e) is false. *)
val negate : inequality -> inequality

(* Solve a system of inequalities.
   Propagates Contradiction if the system is a contradiction. *)
val solve : inequality list -> unit

