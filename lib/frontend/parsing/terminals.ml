open Ast
open Parser

let keyword_token (keyword : Ast.SourceKeywords.t) : Parser.token =
  match keyword with
  | Assert -> SPEC Stmt.Assert
  | Assume -> SPEC Stmt.Assume
  | Au -> AU
  | AuCommit -> AUCOMMIT
  | Atomic -> ATOMIC
  | Axiom -> AXIOM
  | AtomicToken -> ATOMICTOKEN
  | Auto -> AUTO
  | Inline -> INLINE
  | Bool -> CONSTTYPE Type.Bool
  | Case -> CASE
  | Choose -> CHOOSE
  | Checked -> CHECKED
  | Data -> DATA
  | Else -> ELSE
  | Ensures -> ENSURES
  | Exhale -> SPEC Stmt.Exhale
  | Exists -> QUANT Expr.Exists
  | False -> CONSTVAL (Expr.Bool false)
  | Field -> FIELD
  | Forall -> QUANT Expr.Forall
  | Fold -> USE Stmt.Fold
  | Free -> FREE
  | Func -> FUNC Func
  | Ghost -> GHOST
  | Havoc -> HAVOC
  | If -> IF
  | Int -> CONSTTYPE Type.Int
  | Include -> INCLUDE
  | Inhale -> SPEC Stmt.Inhale
  | Interface -> MODULE true
  | Inv -> FUNC Invariant
  | Invariant -> INVARIANT
  | Import -> IMPORT
  | Implicit -> IMPLICIT
  | Lemma -> LEMMA
  | Rep -> REP
  | Map -> TYPECONSTR (Type.Map, 2)
  | Module -> MODULE false
  | New -> NEW
  | Null -> CONSTVAL Expr.Null
  | Opens -> OPENS
  | Own -> OWN
  | Pred -> FUNC Pred
  | Proc -> PROC
  | Ref -> CONSTTYPE Type.Ref
  | Real -> CONSTTYPE Type.Real
  | Requires -> REQUIRES
  | Return -> RETURN
  | Returns -> RETURNS
  | Subseteq -> SUBSETEQ
  | Underscore -> UNDERSCORE
  | Set -> TYPECONSTR (Type.Map, 1)
  | FinSet -> TYPECONSTR (Type.FinSet, 1)
  | Spawn -> SPAWN
  | True -> CONSTVAL (Expr.Bool true)
  | Type -> TYPE
  | Unfold -> USE Stmt.Unfold
  | Val -> VAR true
  | Var -> VAR false
  | Where -> WHERE
  | With -> WITH
  | While -> WHILE
  | Proph_type -> PROPH
  | Resolve -> RESOLVE
  | Proph -> PROPHPRED
  | Decreases -> DECREASES
  | EC -> EC
  | Contra -> ECCONTRA
  | Error -> ECERROR
  | ECFn -> ECFN
  | ECList -> ECLIST
  | ECVal -> ECVAL
  | Rand -> RAND
  | RandEven -> RANDEVEN
  | Is -> IS
  | Match -> MATCH
  | In -> IN

let keyword_table = Hashtbl.create 128

let () =
  List.iter
    (fun (name, keyword) -> Hashtbl.add keyword_table name (keyword_token keyword))
    Ast.SourceKeywords.entries

let negated_keyword_token (keyword : Ast.SourceKeywords.t) =
  match keyword with In -> Some NOTIN | _ -> None

let negated_keywords =
  List.filter_map
    (fun (name, keyword) ->
      Base.Option.map (negated_keyword_token keyword) ~f:(fun token -> (name, token)))
    Ast.SourceKeywords.entries

(* A word may continue past a negated keyword, as in [!inside]. *)
let negated_keyword_prefix word =
  List.fold_left
    (fun found (prefix, token) ->
      let length = String.length prefix in
      if not (Base.String.is_prefix word ~prefix) then found
      else
        match found with
        | Some (previous, _) when previous >= length -> found
        | _ -> Some (length, token))
    None negated_keywords

let operator_table = Hashtbl.create 64

let _ =
  List.iter
    (fun (op, tok) -> Hashtbl.add operator_table op tok)
    [
      ("==>", IMPLIES);
      ("<=>", IFF);
      ("=", EQ);
      ("==", EQEQ);
      ("!=", NEQ);
      ("<=", LEQ);
      (">=", GEQ);
      ("<", LT);
      (">", GT);
      ("||", OR);
      ("&&", AND);
      ("!", NOT);
      ("++", UNION);
      ("--", DIFF);
      ("**", INTER);
      ("+", ADDOP Expr.Plus);
      ("-", MINUS);
      ("/", MULTOP Expr.Div);
      ("*", MULTOP Expr.Mult);
      ("%", MULTOP Expr.Mod);
      (":=", COLONEQ);
      ("::", COLONCOLON);
      (":", COLON);
      (":>", COLONGT);
      (";", SEMICOLON);
      (",", COMMA);
      (".", DOT);
      ("?", QMARK);
      (":|", COLONPIPE);
      ("=>", DARROW);
      ("..", DOTDOT);
    ]
