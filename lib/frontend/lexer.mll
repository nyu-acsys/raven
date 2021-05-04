{
 
open Ast
open Util
open Lexing
open Parser
  
(* set file name *)
let set_file_name lexbuf name =
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = name }


let keyword_table = Hashtbl.create 64
let _ =
  List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
    ([("assert", ASSERT);
      ("assume", ASSUME);
      ("atomic", ATOMIC);
      ("Bool", BOOL);
      ("data", DATA);
      ("else", ELSE);
      ("ensures", ENSURES);
      ("false", CONSTVAL (Expr.Bool false));
      ("forall", QUANT(Expr.Forall));
      ("exists", QUANT(Expr.Exists));
      ("func", FUNC (Func));
      ("ghost", GHOST);
      ("havoc", HAVOC);
      ("if", IF);
      ("Int", INT);
      ("interface", INTERFACE);
      ("invariant", INVARIANT);
      ("implicit", IMPLICIT);
      ("lemma", PROC(Lemma));
      ("Ref", REF);
      ("Map", MAP);
      ("module", MODULE);
      ("new", NEW);
      ("null", CONSTVAL Expr.Null);
      ("pred", FUNC (Func));
      ("procedure", PROC (Proc));
      ("requires", REQUIRES);
      ("return", RETURN);
      ("returns", RETURNS);
      ("struct", STRUCT);
      ("subseteq", SUBSETEQ);
      ("Set", SET);
      ("true", CONSTVAL (Expr.Bool true));
      ("type", TYPE);
      ("val", VAL);
      ("var", VAR);
      ("while", WHILE);
    ])

let operator_table = Hashtbl.create 64
let _ =
  List.iter (fun (op, tok) -> Hashtbl.add operator_table op tok)
    ["==>", IMPLIES;
     "<=>", IFF;
     "==", EQ;
     "!=", NEQ;
     "<=", LEQ;
     ">=", GEQ;
     "<", LT;
     ">", GT;
     "||", OR;
     "&&", AND;
     "in", IN;
     "!in", NOTIN;
     "!", NOT;
     "++", ADDOP Expr.Union;
     "--", DIFF;
     "**", MULTOP Expr.Inter;
     "+", ADDOP Expr.Plus;
     "-", MINUS;
     "/", MULTOP Expr.Div;
     "*", MULTOP Expr.Mult;
     "%", MULTOP Expr.Mod;
     ":=", COLONEQ;
     "::", COLONCOLON;
     ":", COLON;
     ";", SEMICOLON;
     ",", COMMA;
     ".", DOT;
     "?", QMARK;
     ]
    
let lexical_error lexbuf msg =
  let pos = lexeme_start_p lexbuf in
  let loc = Loc.mk_loc pos pos in
  Error.syntax_error loc msg

}

let operator_char = ['+''-''*''/''%''.'':'',''?''>''<''=''&''|''!']
let operator = operator_char+ | "in" | "!in" | "subseteq"
let digit_char = ['0'-'9']
let ident_char = ['A'-'Z''a'-'z''_']
let ident = ident_char ('\'' | ident_char | digit_char)*
let digits = digit_char+

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
| operator as op
    { try
      Hashtbl.find operator_table op
    with Not_found ->
      lexical_error lexbuf (Some("Unknown operator: " ^ op))
    }
| ident as name '#' (digit_char+ as num) { IDENT(Ident.mk_ident name (int_of_string num)) }
| ident as kw
    { try
      Hashtbl.find keyword_table kw
    with Not_found ->
      IDENT (Ident.mk_ident kw 0)
    }
| digits as num { CONSTVAL (Expr.Int (Int64.of_string num)) }
| eof { EOF }
| _ { lexical_error lexbuf None }

and comments level = parse
| "*/" { if level = 0 then token lexbuf
         else comments (level - 1) lexbuf
       }
| "/*" { comments (level + 1) lexbuf }
| '\n' { Lexing.new_line lexbuf; comments (level) lexbuf }
| _ { comments level lexbuf }
| eof { token lexbuf }
