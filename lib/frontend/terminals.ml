open Ast
open Parser
  
let keyword_table = Hashtbl.create 128
let _ =
  List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
    ([("assert", SPEC Stmt.Assert);
      ("assume", SPEC Stmt.Assume);
      ("au", AU);
      ("atomic", ATOMIC);
      ("axiom", AXIOM);
      ("AtomicToken", ATOMICTOKEN);
      ("auto", AUTO);
      ("Bool", CONSTTYPE Type.Bool);
      ("case", CASE);
      ("data", DATA);
      ("else", ELSE);
      ("ensures", ENSURES);
      ("exhale", SPEC Stmt.Exhale);
      ("exists", QUANT(Expr.Exists));
      ("false", CONSTVAL (Expr.Bool false));
      ("forall", QUANT(Expr.Forall));
      ("fold", USE (Stmt.Fold));
      ("field", FIELD);
      ("func", FUNC (Func));
      ("ghost", GHOST);
      ("havoc", HAVOC);
      ("if", IF);
      ("Int", CONSTTYPE Type.Int);
      ("include", INCLUDE);
      ("inhale", SPEC Stmt.Inhale);
      ("interface", MODULE true);
      ("inv", FUNC (Invariant));
      ("invariant", INVARIANT);
      ("import", IMPORT);
      ("implicit", IMPLICIT);
      ("lemma", LEMMA);
      ("rep", REP);
      ("Map", TYPECONSTR (Type.Map, 2));
      ("module", MODULE false);
      ("new", NEW);
      ("null", CONSTVAL Expr.Null);
      ("own", OWN);
      ("Perm", CONSTTYPE Type.Perm);
      ("pred", FUNC (Pred));
      ("proc", PROC);
      ("Ref", CONSTTYPE Type.Ref);
      ("Real", CONSTTYPE Type.Real);
      ("requires", REQUIRES);
      ("return", RETURN);
      ("returns", RETURNS);
      (* ("subseteq", SUBSETEQ); *)
      ("Set", TYPECONSTR (Type.Map, 1));
      ("spawn", SPAWN);
      ("true", CONSTVAL (Expr.Bool true));
      ("type", TYPE);
      ("unfold", USE (Stmt.Unfold));
      ("val", VAR true);
      ("var", VAR false);
      ("with", WITH);
      ("while", WHILE);

      (* ListExt *)
      ("List", LIST); (*Parser.TYPECONSTR (TypeExt (Ext.ListExtInstance.ListConstr), 1));*)

      (* ProphecyExt *)
      ("NewProph", NEWPROPH);
      ("NewProph1", NEWPROPH1);
      ("ResolveProph", RESOLVEPROPH);
      ("prophecy", PROPHECY);
      ("ProphId", PROPHID);

      (* AtomicExt *)
      ("cas", CAS);
      ("faa", FAA);
      ("xchg", XCHG);

      (* ErrorCreditsExt *)
      ("ECContra", ECCONTRA);
      ("ECFn", ECFN);
      ("ECList", ECLIST);
      ("ECVal", ECVAL);
      ("Rand", RAND);
    ])

let operator_table = Hashtbl.create 64
let _ =
  List.iter (fun (op, tok) -> Hashtbl.add operator_table op tok)
    ["==>", IMPLIES;
     "<=>", IFF;
     "=", EQ;
     "==", EQEQ;
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
     "subseteq", SUBSETEQ;
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
     ":|", COLONPIPE;
     "-*-", ERRORCRED;
     ]
