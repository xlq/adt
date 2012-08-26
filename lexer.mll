{

open Parser
open Big_int

let create_hashtable size init =
   let tbl = Hashtbl.create size in
   List.iter (fun (key,data) -> Hashtbl.add tbl key data) init;
   tbl

let keywords = create_hashtable 10 [
   "and",         AND;
   "or",          OR;
   "end",         END;
   "package",     PACKAGE;
   "procedure",   PROCEDURE;
   "null",        NULL;
   "var",         VAR;
   "is",          IS;
   "if",          IF;
   "then",        THEN;
   "else",        ELSE;
   "elsif",       ELSIF;
   "while",       WHILE;
   "loop",        LOOP;
   "type",        TYPE;
   "range",       RANGE;
   "given",       GIVEN;
   "True",        TRUE;
   "False",       FALSE;
   "Inspect_Type", INSPECT_TYPE;
   "Static_Assert", STATIC_ASSERT;
]

}

rule scan = parse
   | [' ' '\t']
      { scan lexbuf }
   | '\n'
      { Lexing.new_line lexbuf; scan lexbuf }
   | "--" [^ '\n']* '\n'
      (* comment *)
      { Lexing.new_line lexbuf; scan lexbuf }
   | ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']* as id
      {
         try Hashtbl.find keywords id
         with Not_found -> IDENT(id)
      }
   | ['0'-'9']+ as value { INTEGER(big_int_of_string value) }
   | '('  { LPAREN }
   | ')'  { RPAREN }
   | '['  { LBRACKET }
   | ']'  { RBRACKET }
   | '{'  { LBRACE }
   | '}'  { RBRACE }
   | ':'  { COLON }
   | ';'  { SEMICOLON }
   | '.'  { DOT }
   | ','  { COMMA }
   | ":=" { ASSIGN }
   | ".." { DOTDOT }
   | "=>" { RARROW }
   | '='  { EQ }
   | "<>" { NE }
   | '<'  { LT }
   | '>'  { GT }
   | "<=" { LE }
   | ">=" { GE }
   | eof  { EOF }
