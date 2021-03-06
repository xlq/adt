(* This package describes the result of the first pass.
   The first pass parses the input file and produces a simple parse
   tree that's almost a direct representation of the input. *)

open Big_int

type loc = Lexing.position
type dotted_name = string list

type translation_unit =
   | Subprogram_unit of subprogram
   | Package_unit of package

and subprogram =
   {
      sub_location      : loc;
      sub_name          : dotted_name;
      sub_parameters    : parameter list;
      sub_constraints   : konstraint list;
      sub_body          : statement;
   }

and parameter =
   {
      param_location : loc;
      param_name     : string;
      param_mode     : Symbols.param_mode;
      param_type     : ttype;
   }

and konstraint =
   {
      constr_mode    : Symbols.param_mode;
      constr_expr    : expr;
   }

and package =
   {
      pkg_location      : loc;
      pkg_name          : dotted_name;
      pkg_declarations  : declaration list;
   }

and declaration =
   | Subprogram of subprogram
   | Type_decl of loc * string * type_decl

and type_decl =
   | Record_type_decl of record_field list

and record_field =
   | Record_constraint of expr
   | Record_field of loc * string * ttype

and ttype =
   | Named_type of loc * dotted_name

and statement =
   | No_statement of loc (* no statement (end of statements/...) *)
   | Null_statement of loc (* the statement "null;" *)
   | Assignment of loc * expr (* destination *)
                       * expr (* source *)
                       * statement          (* continuation *)
   | If_statement of loc * expr (* condition *)
                        * statement  (* true part *)
                        * statement  (* false part *)
                        * statement  (* continuation *)
   | While_loop of loc * expr (* condition *)
                       * statement  (* body *)
                       * statement  (* continuation *)
   | Subprogram_call of loc * dotted_name * arguments * statement
   | Inspect_type of loc * dotted_name * statement
   | Static_assert of loc * expr * statement

and arguments = expr list             (* positional *)
              * (string * expr) list  (* named *)

and expr =
   | Name of loc * dotted_name
   | Boolean_literal of loc * bool
   | Integer_literal of loc * big_int
   | Comparison of loc * Symbols.comparison * expr * expr
