{
 
open Ast
open Util
open Lexing
open Parser
  
(* set file name *)
let set_file_name lexbuf name =
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = name }
    
let lexical_error lexbuf msg =
  let pos = lexeme_start_p lexbuf in
  let loc = Loc.make pos pos in
  Error.syntax_error loc msg

}

let operator_char = ['+''-''*''%''.'':'',''?''>''<''=''&''|''!']
let operator = '/' | ';' | operator_char+ | "in" | "!in" | "subseteq"
let digit_char = ['0'-'9']
let ident_char = ['A'-'Z''a'-'z''_']
let lowercase_char = ['a'-'z''_']
let uppercase_char = ['A'-'Z']
let ident = lowercase_char ('\'' | ident_char | digit_char)*
let mod_ident = uppercase_char ('\'' | ident_char | digit_char)*
let digits = digit_char+
let float = digits '.' digits

rule token = parse
  [' ' '\t'] { token lexbuf }
| '\n' { Lexing.new_line lexbuf; token lexbuf }
| "//" [^ '\n']* { token lexbuf }
| "/*" { comments 0 lexbuf }
| "{|" { LBRACEPIPE }
| "|}" { RBRACEPIPE }
| "[|" { LBRACKETPIPE }
| "|]" { RBRACKETPIPE }
| '(' { LPAREN }
| ')' { RPAREN }
| '{' { LBRACE }
| '}' { RBRACE }
| '[' { LBRACKET }
| ']' { RBRACKET }
| "{!" { LGHOSTBRACE }
| "!}" { RGHOSTBRACE }
| "\"" (( ("\\" _) | [^ '"'] )* as str) "\"" { STRINGVAL (Scanf.unescaped str) }
| operator as op
    { try
      Hashtbl.find Terminals.operator_table op
    with Not_found ->
      lexical_error lexbuf ("Unknown operator: " ^ op)
  }
| '#' (digit_char+ as num) { HASH(Int64.of_string num) }
| ident as name '^' (digit_char+ as num) { IDENT(Ident.make (Loc.make lexbuf.lex_start_p lexbuf.lex_curr_p) name (int_of_string num)) }
| mod_ident as kw
    { try
      Hashtbl.find Terminals.keyword_table kw
    with Not_found ->
      MODIDENT (Ident.make (Loc.make lexbuf.lex_start_p lexbuf.lex_curr_p) kw 0)
    }
| ident as kw
    { try
      Hashtbl.find Terminals.keyword_table kw
    with Not_found ->
      IDENT (Ident.make (Loc.make lexbuf.lex_start_p lexbuf.lex_curr_p) kw 0)
    }
| digits as num { CONSTVAL (Expr.Int (Int64.of_string num)) }
| float as num { CONSTVAL (Expr.Real (Float.of_string num)) }
| eof { EOF }
| _ { lexical_error lexbuf "Unexpected character" }

and comments level = parse
| "*/" { if level = 0 then token lexbuf
         else comments (level - 1) lexbuf
       }
| "/*" { comments (level + 1) lexbuf }
| '\n' { Lexing.new_line lexbuf; comments (level) lexbuf }
| _ { comments level lexbuf }
| eof { token lexbuf }
