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

(* --- Automatic semicolon insertion ---

   A semicolon is only ever meaningful in two places in the grammar: terminating a statement in
   the body of a proc/lemma, and (optionally) separating the case branches of a data type
   declaration. Everywhere else -- a callable's requires/ensures/invariant clauses, a module or
   callable header split across lines, a sequence of include directives, the members of a module
   body -- consecutive entries are separated by nothing but whitespace, with no semicolon wanted
   or tolerated. This means a newline only ever needs to be considered for insertion while lexing
   inside a statement list; everywhere else it is unconditionally just whitespace, regardless of
   what precedes or follows it. [lex_state] is threaded functionally through every call below (no
   mutable state) and tracks exactly this:

   - [scopes] is a stack (innermost first) of the kind of each currently-open parenthesis,
     bracket, pipe-bracket, ghost-brace, or plain-brace group:
       - [Group], for a parenthesis/bracket/pipe-bracket group, a func/pred/invariant body, or a
         data type's variant list (the latter two only because they may contain further nested
         groups, e.g. a quantifier trigger, that must also suppress insertion; the body/variant
         list's own separators need no help from insertion, since the grammar already allows
         nothing between consecutive entries there).
       - [Loop_header], for a while loop's condition parenthesis, and afterwards for the (possibly
         empty) span of invariant clauses that follows it up to the loop's body: this is not a
         group, but it isn't a statement list either, since it isn't preceded by any body-opening
         keyword to classify a brace by -- the loop's body brace is only recognized as such when
         it directly follows a complete-looking token (see [next_brace_kind] below), as opposed to
         a quantifier trigger nested inside an invariant's expression, which never is.
       - [Module_list], for a module body: nothing (semicolon or otherwise) separates its members.
       - [Stmt_list], for a proc/lemma body or a nested block/loop body: the only scope in which a
         newline may become a semicolon.
     The stack starts empty, which behaves like [Group] (or, equivalently, like top level before
     any module has been entered) for insertion purposes: never insert.
   - [last_token_can_end_stmt] records whether the most recently lexed token could plausibly be
     the last token of a complete statement or expression (an identifier, literal, a closing
     paren or bracket, or a bare `return`) as opposed to one that necessarily expects more to
     follow (an infix operator, a keyword like if, a comma, etc). Insertion only happens when this
     is true; it also disambiguates a loop's body brace (preceded by such a token) from a trigger
     nested in an invariant (preceded by :: or a previous trigger's closing brace, neither of
     which qualifies).
   - [next_brace_kind] classifies the next plain brace lexed, whenever that ends up being: [Group]
     if the most recently seen relevant keyword was func/pred/inv or a data type's, [Module_list]
     if it was a module's, [Stmt_list] if it was proc/lemma/axiom, and inferred from the current
     scope otherwise (covering a nested block/loop body, and a trigger nested in a func body).
   - [next_paren_is_loop_cond] records whether the next '(' lexed opens a while loop's condition
     (set right after seeing [WHILE], consumed by that very next '(').
   - [next_lt_opens_atomic_token]/[in_atomic_token_brackets] track the same way, for
     [AtomicToken<P>]'s '<'/'>' pair -- the one place these lex as a closing delimiter rather
     than the comparison operator LT/GT ordinarily do, so a statement ending in [AtomicToken<P>]
     can have [last_token_can_end_stmt] set on its '>' the same as a closing paren/bracket would.

   One case needs a single token of lookahead rather than being decidable from [lex_state] alone:
   a multi-line ternary split right after '?' and again right after ':' can leave a branch
   expression (e.g. a bare identifier) looking like a complete statement in its own right, even
   though the following line's leading ':' shows it was only the first half of the ternary. Since
   ':' can never legally start a statement, seeing it is an unambiguous signal to suppress
   insertion regardless of what preceded the newline. [on_newline] and [make_token] handle the
   mechanics of this lookahead (see their comments below); every other decision in this file
   remains a pure function of [lex_state] and the current token. *)

type scope_kind = Group | Loop_header | Module_list | Stmt_list

type lex_state = {
  scopes : scope_kind list;
  last_token_can_end_stmt : bool;
  next_brace_kind : scope_kind option;
  next_paren_is_loop_cond : bool;
  (* Same lookahead-free trick as [next_paren_is_loop_cond]/[Loop_header]: [AtomicToken<P>]
     (parser.mly's [ATOMICTOKEN LT qid = qual_ident GT]) is the only place '<'/'>' are a
     closing delimiter pair rather than the comparison operator LT/GT ordinarily lex as.
     [next_lt_opens_atomic_token] is set on [ATOMICTOKEN], consumed by the very next [LT];
     [in_atomic_token_brackets] is set by that [LT], consumed by the matching [GT]. Without
     this, a statement ending in [AtomicToken<P>] (e.g. a bare `var tok: AtomicToken<P>`
     declaration) never got its semicolon inserted, since a trailing '>' otherwise always
     looks like an unfinished comparison awaiting its right operand. *)
  next_lt_opens_atomic_token : bool;
  in_atomic_token_brackets : bool;
}

let initial_state =
  { scopes = [];
    last_token_can_end_stmt = false;
    next_brace_kind = None;
    next_paren_is_loop_cond = false;
    next_lt_opens_atomic_token = false;
    in_atomic_token_brackets = false;
  }

(* Computes the state to carry forward after producing [tok], given the state [st] beforehand. *)
let advance st (tok : Parser.token) =
  let scopes =
    match tok with
    | LPAREN -> (if st.next_paren_is_loop_cond then Loop_header else Group) :: st.scopes
    | LBRACKET | LBRACEPIPE | LBRACKETPIPE -> Group :: st.scopes
    | LGHOSTBRACE -> Stmt_list :: st.scopes
    | RPAREN ->
        (match st.scopes with
         (* The loop condition just closed: what follows (invariant clauses, then the body) is
            neither a group nor (yet) a statement list. *)
         | Loop_header :: rest -> Loop_header :: rest
         | _ :: rest -> rest
         | [] -> [])
    | RBRACKET | RBRACEPIPE | RBRACKETPIPE | RGHOSTBRACE ->
        (match st.scopes with _ :: rest -> rest | [] -> [])
    | LBRACE ->
        (match st.scopes with
         | Loop_header :: rest when st.last_token_can_end_stmt ->
             (* A complete-looking token (the last invariant's expression, or the bare condition
                if there are none) just precedes this brace: it's the loop's own body. A trigger
                pattern nested in an invariant's expression is never preceded by such a token (::
                or a previous trigger's closing brace precede it instead), so is not mistaken for
                one here. *)
             Stmt_list :: rest
         | scopes ->
             let kind =
               match st.next_brace_kind with
               | Some k -> k
               | None -> (match scopes with Group :: _ | Loop_header :: _ -> Group | _ -> Stmt_list)
             in
             kind :: scopes)
    | RBRACE -> (match st.scopes with _ :: rest -> rest | [] -> [])
    | _ -> st.scopes
  in
  let next_brace_kind =
    match tok with
    (* [MATCH] for the same reason as [DATA]: a `match`'s arm list is a `case` list just
       like a variant list, whose own separators the grammar already tolerates without
       help from insertion. Classifying it matters because [next_brace_kind] is sticky --
       inside a `proc`, the pending [Stmt_list] set by [PROC] would otherwise be claimed
       by the *match's* brace rather than the body's, turning each arm-ending newline
       into a semicolon and leaving a trailing one before the closing brace. *)
    | FUNC _ | DATA | MATCH -> Some Group
    | MODULE _ -> Some Module_list
    | PROC | LEMMA | AXIOM -> Some Stmt_list
    | LBRACE -> None (* consumed; the next one is classified afresh *)
    | _ -> st.next_brace_kind
  in
  let next_paren_is_loop_cond =
    match tok with
    | WHILE -> true
    | LPAREN -> false (* consumed, whether or not it triggered [Loop_header] above *)
    | _ -> st.next_paren_is_loop_cond
  in
  let next_lt_opens_atomic_token =
    match tok with
    | ATOMICTOKEN -> true
    | LT -> false (* consumed, whether or not it triggered [in_atomic_token_brackets] below *)
    | _ -> st.next_lt_opens_atomic_token
  in
  let in_atomic_token_brackets =
    match tok with
    | LT -> st.next_lt_opens_atomic_token
    | GT -> false (* consumed *)
    | _ -> st.in_atomic_token_brackets
  in
  let last_token_can_end_stmt =
    match tok with
    | IDENT _ | MODIDENT _ | CONSTVAL _ | CONSTTYPE _ | ATOMICTOKEN
    | STRINGVAL _ | HASH _
    | RPAREN | RBRACKET | RBRACEPIPE | RBRACKETPIPE
    (* Unlike every other keyword here, `return` can legally end a statement
       on its own -- a return with no values, from a callable with no `returns`
       clause. A `return` with values is always followed by at least one more
       token before the next newline, so this can't misfire on those. *)
    | RETURN -> true
    (* The closing '>' of [AtomicToken<P>] -- see [in_atomic_token_brackets]'s doc comment.
       [st], not the freshly-computed [in_atomic_token_brackets] above, since what matters is
       whether *this* '>' was the closing one, i.e. the state as of just before it. *)
    | GT when st.in_atomic_token_brackets -> true
    | _ -> false
  in
  { scopes; last_token_can_end_stmt; next_brace_kind; next_paren_is_loop_cond;
    next_lt_opens_atomic_token; in_atomic_token_brackets }

(* Produces [tok], pairing it with the state to carry forward after it, and no buffered
   follow-up token (see [on_newline] for the one case that needs one). *)
let emit st (tok : Parser.token) = advance st tok, tok, None

(* Decides, given the state [st] as of just before a newline (i.e. reflecting the last real
   token lexed), whether that newline should be interpreted as a semicolon. Deciding this needs
   one token of lookahead in exactly one case: when the next token is ':', which can never
   legally start a statement, so it must instead be continuing an expression begun on the
   previous line -- e.g. a multi-line ternary split right after '?' and again right after ':',
   where the '?' branch (say, a bare identifier) looks like a complete statement in its own
   right. [peek] lexes that one lookahead token; since doing so unavoidably consumes it from the
   buffer, it is threaded back out as a third, optional "replay this token next" component, which
   the ['\n'] rule pairs with the lookahead's own source positions and [make_token] then returns
   verbatim on its following call instead of touching the lexbuf again. *)
let on_newline st ~peek =
  match st.scopes with
  | Stmt_list :: _ when st.last_token_can_end_stmt ->
      let st', tok, _ = peek { st with last_token_can_end_stmt = false } in
      (match tok with
       | COLON -> Some (st', tok, None)
       | _ -> Some (advance st SEMICOLON, SEMICOLON, Some (st', tok)))
  | _ -> None

}

(* A carriage return is only ever recognized as part of a line terminator, so a
   stray one remains the lexical error it always was. *)
let newline = '\r'? '\n'
(* `,` is deliberately excluded: unlike every character here, it never combines with a
   neighbor to form a longer operator (see Terminals.operator_table), so folding it into
   [operator_char+]'s maximal munch only ever causes harm -- e.g. `AtomicToken<P>,` lexing
   `>,` as one (unregistered, and hence rejected) two-character candidate operator, instead
   of `>` and `,` separately, whenever a `>` or another operator character is immediately
   followed by a comma with no space. Matched as its own single-character alternative below,
   the same way `;` already is, for exactly this reason. *)
let operator_char = ['+''-''*''%''.'':''?''>''<''=''&''|''!']
let operator = '/' | ';' | ',' | operator_char+ | "in" | "!in" | "subseteq"
let digit_char = ['0'-'9']
let ident_char = ['A'-'Z''a'-'z''_']
let lowercase_char = ['a'-'z''_']
let uppercase_char = ['A'-'Z']
let ident = lowercase_char ('\'' | ident_char | digit_char)*
let mod_ident = uppercase_char ('\'' | ident_char | digit_char)*
let digits = digit_char+
let float = digits '.' digits

rule token_lex st = parse
  [' ' '\t'] { token_lex st lexbuf }
| newline {
    (* Where an inserted semicolon belongs: the line break itself, i.e. just past
       the last token on the line being ended -- the carriage return of a CRLF
       pair, where there is one, being part of that break rather than of the
       line's text. *)
    let nl_pos = lexbuf.lex_start_p in
    Lexing.new_line lexbuf;
    match on_newline st ~peek:(fun st -> token_lex st lexbuf) with
    | Some (st', tok, None) -> st', tok, None
    | Some (st', tok, Some (pending_st, pending_tok)) ->
        (* Deciding to insert consumed the lookahead token, leaving the lexbuf's
           positions describing *it* -- so menhir would give the inserted
           SEMICOLON, and hence the statement it terminates, an end position on
           the next line, past the token that starts the next statement. Report
           the semicolon at the line break instead, and stash the lookahead's own
           positions to be restored when it is replayed. That restore also puts
           [lex_curr_p] back the way [Lexing.engine] left it, before the next
           token is scanned from it. *)
        let pending_start_p = lexbuf.lex_start_p in
        let pending_curr_p = lexbuf.lex_curr_p in
        lexbuf.lex_start_p <- nl_pos;
        lexbuf.lex_curr_p <- nl_pos;
        st', tok, Some (pending_st, pending_tok, pending_start_p, pending_curr_p)
    | None -> token_lex st lexbuf
  }
| "//" [^ '\n' '\r']* { token_lex st lexbuf }
| "/*" { comments 0 st lexbuf }
| "{|" { emit st LBRACEPIPE }
| "|}" { emit st RBRACEPIPE }
| "[|" { emit st LBRACKETPIPE }
| "|]" { emit st RBRACKETPIPE }
| '(' { emit st LPAREN }
| ')' { emit st RPAREN }
| '{' { emit st LBRACE }
| '}' { emit st RBRACE }
| '[' { emit st LBRACKET }
| ']' { emit st RBRACKET }
| "{!" { emit st LGHOSTBRACE }
| "!}" { emit st RGHOSTBRACE }
| "\"" (( ("\\" _) | [^ '"'] )* as str) "\"" { emit st (STRINGVAL (Scanf.unescaped str)) }
| operator as op
    { try
      emit st (Hashtbl.find Terminals.operator_table op)
    with Not_found ->
      (* A user-declarable symbolic operator: not one of the reserved strings in
         [Terminals.operator_table], but still a maximal run of [operator_char]s.
         Classified into a token per Scala's rule (Scala Language Spec SS6.12.3) --
         an operator ending in ':' is right-associative regardless of its leading
         character (matching how `::` itself already behaves); otherwise the
         leading character alone picks the tier, mirroring the tier cascade the
         grammar already has (`*`/`%` -> mult_expr, `+`/`-` -> add_expr, `<`/`>`
         -> the chainable comp_op tier, `=`/`!` -> eq_expr, `&` -> and_expr, `|`
         -> or_expr). A leading `.`/`?`/`:' has no tier to classify into (`:` alone
         is only reachable here for a single ':' followed immediately by another
         `operator_char`, since a solitary `:` is itself already reserved) and is
         rejected rather than guessed at. *)
      let loc = Loc.make lexbuf.lex_start_p lexbuf.lex_curr_p in
      let ident = Ident.make loc op 0 in
      let last = op.[String.length op - 1] in
      if Char.equal last ':' then emit st (RABINOPSYM ident)
      else
        match op.[0] with
        | '*' | '%' -> emit st (MULTOPSYM ident)
        | '+' | '-' -> emit st (ADDOPSYM ident)
        | '<' | '>' -> emit st (RELOPSYM ident)
        | '=' | '!' -> emit st (EQOPSYM ident)
        | '&' -> emit st (ANDOPSYM ident)
        | '|' -> emit st (OROPSYM ident)
        | _ -> lexical_error lexbuf ("Unknown operator: " ^ op)
  }
| '#' (digit_char+ as num) { emit st (HASH(Int64.of_string num)) }
| ident as name '^' (digit_char+ as num) { emit st (IDENT(Ident.make (Loc.make lexbuf.lex_start_p lexbuf.lex_curr_p) name (int_of_string num))) }
| mod_ident as kw
    { try
      emit st (Hashtbl.find Terminals.keyword_table kw)
    with Not_found ->
      emit st (MODIDENT (Ident.make (Loc.make lexbuf.lex_start_p lexbuf.lex_curr_p) kw 0))
    }
| ident as kw
    { try
      emit st (Hashtbl.find Terminals.keyword_table kw)
    with Not_found ->
      emit st (IDENT (Ident.make (Loc.make lexbuf.lex_start_p lexbuf.lex_curr_p) kw 0))
    }
| digits as num { emit st (CONSTVAL (Expr.Int (Int64.of_string num))) }
| float as num { emit st (CONSTVAL (Expr.Real (Float.of_string num))) }
| eof { st, EOF, None }
| _ { lexical_error lexbuf (Printf.sprintf "Unexpected character '%c'" (lexeme_char lexbuf 0)) }

and comments level st = parse
| "*/" { if level = 0 then token_lex st lexbuf
         else comments (level - 1) st lexbuf
       }
| "/*" { comments (level + 1) st lexbuf }
| newline { Lexing.new_line lexbuf; comments level st lexbuf }
| _ { comments level st lexbuf }
| eof { st, EOF, None }

{
(* [make_token ()] returns a fresh, self-contained token supplier of the type menhir expects
   ([Lexing.lexbuf -> Parser.token]), starting from [initial_state]. Calling it again (e.g. for
   the next file) starts over with a fresh state -- there is no global state to reset.

   The one token of state carried between calls beyond [lex_state] itself is a possible buffered
   token: [on_newline] occasionally has to look one token ahead to decide whether to insert a
   semicolon, which unavoidably consumes that lookahead token from the buffer; when that happens
   it is stashed here, along with its own source positions, and replayed on the following call
   instead of lexing afresh. Restoring those positions is what keeps the inserted semicolon's
   own position (the line break -- see the ['\n'] rule) from displacing the lookahead's. *)
let make_token () =
  let state = ref (initial_state, None) in
  fun lexbuf ->
    match !state with
    | _, Some (st', tok, start_p, curr_p) ->
        state := (st', None);
        lexbuf.lex_start_p <- start_p;
        lexbuf.lex_curr_p <- curr_p;
        tok
    | st, None ->
        let st', tok, pending = token_lex st lexbuf in
        state := (st', pending);
        tok
}
