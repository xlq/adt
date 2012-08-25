%{

type pos = Lexing.position

open Parsing
open Parse_tree
open Errors

let pos () = symbol_start_pos ()

let string_of_dotted_name = String.concat "."

let check_end (pos1, name1) (pos2, name2) =
    if name1 <> name2 then
        syntax_error pos2
            ("`end " ^ string_of_dotted_name name2
                ^ ";' should be `end "
                ^ string_of_dotted_name name1 ^ ";'.")

%}

%token <string> IDENT
%token <Big_int.big_int> INTEGER

/* Keywords */
%token PROCEDURE NULL END AND OR VAR IS IF THEN ELSE ELSIF
%token WHILE LOOP TYPE RANGE GIVEN TRUE FALSE
%token INSPECT_TYPE STATIC_ASSERT

/* Punctuation */
%token COLON SEMICOLON DOT DOTDOT COMMA ASSIGN RARROW
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token EQ NE LT LE GT GE

/* Other */
%token EOF

%nonassoc EQ NE LT LE GT GE

%start subprogram
%type <Parse_tree.subprogram> subprogram

%%

dotted_name:
   | IDENT { [$1] }
   | IDENT DOT dotted_name { $1 :: $3 }

ttype:
   | dotted_name { Named_type(pos(), $1) }

subprogram:
   | PROCEDURE dotted_name opt_parameters IS
         ne_statements
     END dotted_name SEMICOLON
      {
         check_end (rhs_start_pos 2, $2) (rhs_start_pos 7, $7);
         {
            sub_location      = pos ();
            sub_name          = $2;
            sub_parameters    = fst $3;
            sub_preconditions = snd $3;
            sub_body          = $5;
         }
      }

opt_parameters:
   | /* empty */ { ([], []) }
   | LPAREN parameters RPAREN { $2 }

parameters:
   | parameter
      { ([$1], []) }
   | expr
      { ([], [$1]) }
   | parameter SEMICOLON parameters
      { ($1::fst $3, snd $3) }
   | expr SEMICOLON parameters
      { (fst $3, $1::snd $3) }

parameter:
   | IDENT COLON ttype
      {
         {
            param_location = pos ();
            param_name     = $1;
            param_type     = $3
         }
      }

ne_statements:
   | NULL SEMICOLON
      { Null_statement(pos ()) }
   | expr ASSIGN expr SEMICOLON statements
      { Assignment(pos (), $1, $3, $5) }
   | if_statement { $1 }
   | while_loop { $1 }
   | INSPECT_TYPE dotted_name SEMICOLON statements
      { Inspect_type(pos (), $2, $4) }
   | STATIC_ASSERT expr SEMICOLON statements
      { Static_assert(pos (), $2, $4) }

statements:
   | /* empty */ { No_statement(pos ()) }
   | ne_statements { $1 }

if_statement:
   | IF expr THEN ne_statements else_parts statements
      { If_statement(pos (), $2, $4, $5, $6) }

else_parts:
   | ELSIF expr THEN ne_statements else_parts
      { If_statement(pos (), $2, $4, $5, No_statement(rhs_end_pos 5)) }
   | ELSE ne_statements END IF SEMICOLON
      { $2 }
   | END IF SEMICOLON
      { No_statement(rhs_start_pos 1) }

while_loop:
   | WHILE expr LOOP
         ne_statements
     END LOOP SEMICOLON statements
      { While_loop(pos (), $2, $4, $8) }

expr:
   | dotted_name  { Name(pos (), $1) }
   | INTEGER      { Integer_literal(pos (), $1) }
   | TRUE         { Boolean_literal(pos (), true) }
   | FALSE        { Boolean_literal(pos (), false) }
   | expr EQ expr { Comparison(rhs_end_pos 2, Symbols.EQ, $1, $3) }
   | expr NE expr { Comparison(rhs_end_pos 2, Symbols.NE, $1, $3) }
   | expr LT expr { Comparison(rhs_end_pos 2, Symbols.LT, $1, $3) }
   | expr GT expr { Comparison(rhs_end_pos 2, Symbols.GT, $1, $3) }
   | expr LE expr { Comparison(rhs_end_pos 2, Symbols.LE, $1, $3) }
   | expr GE expr { Comparison(rhs_end_pos 2, Symbols.GE, $1, $3) }
