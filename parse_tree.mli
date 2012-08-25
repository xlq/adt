(* This package describes the result of the first pass.
   The first pass parses the input file and produces a simple parse
   tree that's almost a direct representation of the input. *)

open Big_int

type file_location = Lexing.position
type loc = file_location
type dotted_name = string list

type subprogram =
   {
      sub_location      : loc;
      sub_name          : dotted_name;
      sub_parameters    : parameter list;
      sub_preconditions : expr list;
      sub_body          : statement;
   }

and parameter =
   {
      param_location : loc;
      param_name     : string;
      param_type     : ttype;
   }

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
   | Inspect_type of loc * dotted_name * statement
   | Static_assert of loc * expr * statement

and expr =
   | Name of loc * dotted_name
   | Boolean_literal of loc * bool
   | Integer_literal of loc * big_int
   | Operation of loc * Symbols.operator * expr * expr
