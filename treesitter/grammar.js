const IDENTIFIER = token(/(\p{XID_Start}|\$|_|\\u[0-9A-Fa-f]{4}|\\U[0-9A-Fa-f]{8})(\p{XID_Continue}|\$|\\u[0-9A-Fa-f]{4}|\\U[0-9A-Fa-f]{8})*/);
const FIELD = token("field");
const COLON = choice(token("colon"), token(":"))
const PRED = token("pred");
const LCURLY = token("{");
const RCURLY = token("}");
const FORALL = token("forall");
const EXISTS = token("exists");
const FALSE = token("false");
const TRUE = token("true");
const IMPLIES = token("==>");
const IFF = token("<=>");
const EQ = token("=");
const EQEQ = token("==");
const NEQ = token("!=");
const LEQ = token("<=");
const GEQ = token(">=");
const LT = token("<");
const GT = token(">");
const OR = token("||");
const AND = token("&&");
const NOT = token("!");
const QUANTIFIER = choice(FORALL, EXISTS)
const PROC = token("proc");
const REQUIRES = token("requires");
const ENSURES = token("ensures");
const IF = token("if");
const ELSE = token("else");
const FOLD = token("fold");
const UNFOLD = token("unfold");
const VAR = token("var");
const ASSERT = token("assert");
const ASSUME = token("assume");
const HAVOC = token("havoc");
const WHILE = token("while");
const INVARIANT = token("invariant");
const COLONEQ = token(":=");
const RETURNS = token("returns");
const RETURN = token("return");
const COLONCOLON = token("::");
const VAL = token("val");

const IN = token("in");
const NOTIN = token("!in");
const ADDOP = token(choice("++", "+"));
const DIFF = token("--");
const MULTOP = token(choice("**", choice("/", choice("*", "%"))));
const MINUS = token("-");
const SEMICOLON = token(";");
const COMMA = token(",");
const DOT = token(".");
const QMARK = token("?");
const COLONPIPE = token(":|");
const WITH = token("with");

module.exports = grammar({
    name: "raven",

    extras: ($) => [/(\s|\f)/, $.comment, $.block_comment], // Ignore whitespace, comments

    rules: {
        source_file: ($) => repeat($.defn),
        defn: ($) => choice($.rep_defn, $.func_defn, $.axiom_defn, $.pred_defn, $.lemma_defn, $.proc_defn, $.field_defn, $.val_defn, $.interface_defn),
        interface_defn: ($) => seq(token("interface"), $.identifier, optional($.type_cons), $.interface_body),
        interface_body: ($) => seq(token("{"), repeat($.defn), token("}")),
        rep_defn: ($) => seq(token("rep"), token("type"), $.identifier),
        func_defn: ($) => seq(token("func"), $.identifier, $.arglist, $.returns_clause, optional($.proc_body)),
        axiom_defn: ($) => seq(optional("auto"), token("axiom"), $.identifier, $.arglist, repeat($.io_spec_clause)),
        lemma_defn: ($) => seq(optional("auto"), token("lemma"), $.identifier, $.arglist, repeat($.io_spec_clause), $.proc_body),
        type_con: ($) => seq($.identifier, token(":"), $.identifier),
        type_cons: ($) => seq(token("["), repeat($.type_con), token("]")),
        val_defn: ($) => seq(repeat($.modifiers), VAL, $.identifier, COLON, $.type, optional(seq(token("="), $.expr))),
        field_defn: ($) => seq(FIELD, $.identifier, COLON, $.identifier),
        pred_defn: ($) => seq(PRED, $.identifier, $.arglist, optional($.pred_body)),
        proc_defn: ($) => seq(PROC, $.identifier, $.arglist, repeat(choice($.io_spec_clause, $.returns_clause)), optional($.proc_body)),
        io_spec_clause: ($) => choice(seq(REQUIRES, $.expr), seq(ENSURES, $.expr)),
        returns_clause: ($) => seq(RETURNS, $.arglist),
        proc_body: ($) => seq(token("{"), repeat(seq($.stmt, token(";"))), optional($.stmt), token("}")),
        stmt: ($) => choice($.stmt_syntax, $.call),
        stmt_syntax: ($) => prec.dynamic(20, choice($.if_stmt, $.while_stmt, $.fold_stmt, $.unfold_stmt, $.var_dec, $.assert_stmt, $.assume_stmt, $.havoc_stmt, $.assign_stmt, $.return_stmt)),
        call: ($) => prec.dynamic(19, seq($.expr)),
        return_stmt: ($) => RETURN,
        assign_stmt: ($) => seq($.location, COLONEQ, $.expr),
        assert_stmt: ($) => seq(ASSERT, $.expr, optional($.with_stmt)),
        with_stmt: ($) => seq(WITH, $.proc_body),
        assume_stmt: ($) => seq(ASSUME, $.expr),
        havoc_stmt: ($) => seq(HAVOC, $.expr),
        if_stmt: ($) => seq(IF, $.paren_expr, $.proc_body, repeat($.elif_clause), optional($.else_clause)),
        elif_clause: ($) => seq(ELSE, IF, $.paren_expr, $.proc_body),
        else_clause: ($) => seq(ELSE, $.proc_body),
        while_stmt: ($) => seq(WHILE, optional($.paren_expr), repeat($.invariant_spec_clause), $.proc_body),
        invariant_spec_clause: ($) => seq(INVARIANT, $.expr),
        fold_stmt: ($) => seq(FOLD, $.expr),
        unfold_stmt: ($) => seq(UNFOLD, $.expr),
        var_dec: ($) => seq(repeat($.modifiers), VAR, $.arg, optional(seq(choice(token(":="), token("=")), $.expr))),
        arglist: ($) => seq(token("("), repeat(seq($.arg, choice(token(","), token(";")))), optional($.arg), token(")")),
        arg: ($) => seq(repeat($.modifiers), $.identifier, COLON, $.type),
        modifiers: ($) => choice(token("implicit"), token("ghost")),
        type: ($) => choice($.identifier, $.type_application),
        type_application: ($) => seq($.identifier, token("["), $.typelist, token("]")),
        typelist: ($) => seq(repeat(seq($.type, ",")), $.type),
        pred_body: ($) => seq(LCURLY, $.expr, RCURLY),
        expr: ($) => choice($.value, $.unop, $.binop, $.ternary_op, $.quantified_expr, $.paren_expr, $.apply, $.update, $.lookup, $.map_literal),
        map_literal: ($) => seq(token("{|"), $.arg, COLONCOLON, $.expr, token("|}")),
        update: ($) => prec(8, seq($.expr, token("["), $.expr, COLONEQ, $.expr, token("]"))),
        apply: ($) => prec(10, seq($.expr, token("("), repeat(seq($.expr, token(","))), optional($.expr), token(")"))),
        lookup: ($) => prec(9, seq($.expr, token("["), repeat(seq($.expr, token(","))), optional($.expr), token("]"))),
        paren_expr: ($) => prec(3, seq(token("("), $.expr, token(")"))),
        value: ($) => choice(seq(optional(token("-")), /\d+|\d*\.\d+/), TRUE, FALSE, $.location),
        unop: ($) => prec(2, seq(NOT, $.expr)),
        binop: ($) => prec.left(1, seq($.expr, $.binop_op, $.expr)),
        binop_op: ($) => choice(IMPLIES, IFF, EQ, EQEQ, NEQ, LEQ, GEQ, LT, GT, OR, AND, ADDOP, DIFF, MINUS, MULTOP),
        ternary_op: ($) => prec.left(1, seq($.expr, token("?"), $.expr, COLON, $.expr)),
        quantified_expr: ($) => prec(7, seq(QUANTIFIER, seq($.arg, repeat(seq(", ", $.arg))), COLONCOLON, optional($.trigger), $.expr)),
        trigger: ($) => seq(token("{"), repeat(seq($.expr, token(","))), $.expr, token("}")),
        location: ($) => seq(repeat(seq($.expr, token("."))), $.identifier),
        identifier: ($) => prec.left(100, seq(IDENTIFIER, repeat(seq(token("."), IDENTIFIER)))),
        block_comment: $ => seq(
            "/*",
            optional($.comment_text),
            "*/"
        ),
        comment_text: $ => repeat1(choice(/.|\n|\r/)),
        comment: _ => seq('//', /(\\+(.|\r?\n)|[^\\\n])*/),
    },
    conflicts: ($) => [[$.location]],
});

const AU = token("au");
const ATOMIC = token("atomic");
const AXIOM = token("axiom");
const ATOMICTOKEN = token("AtomicToken");
const AUTO = token("auto");
const BOOL = token("Bool");
const CAS = token("cas");
const CASE = token("case");
const CLOSEINV = token("closeInv");
const DATA = token("data");
const EXHALE = token("exhale");
const FUNC = token("func");
const GHOST = token("ghost");
const INT = token("Int");
const INCLUDE = token("include");
const INHALE = token("inhale");
const INTERFACE = token("interface");
const INV = token("inv");
const IMPORT = token("import");
const IMPLICIT = token("implicit");
const LEMMA = token("lemma");
const REP = token("rep");
const MAP = token("Map");
const MODULE = token("module");
const NEW = token("new");
const NULL = token("null");
const OPENINV = token("openInv");
const OWN = token("own");
const PERM = token("Perm");
const REF = token("Ref");
const REAL = token("Real");
const SUBSETEQ = token("subseteq");
const SET = token("Set");
const TYPE = token("type");



