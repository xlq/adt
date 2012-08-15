(* Text formatting for dumping expressions, etc. *)

type formatter

(* Create a new formatter. *)
val new_formatter : unit -> formatter

(* Increase/decrease the current indentation level. *)
val indent  : formatter -> unit
val undent  : formatter -> unit

(* Put a string. The string must not contain line breaks. *)
val puts    : formatter -> string -> unit

(* Put a line break. *)
val break   : formatter -> unit

(* Return the formatted text. *)
val get_fmt_str : formatter -> string

(* fencepost f g l - Call g for each item in l.
   After each iteration except the last, call
   f. This is useful for formatting delimited lists. *)
val fencepost : (unit -> unit) -> ('a -> unit) -> 'a list -> unit
