function intervals_exclude(intervals, i) // intervals are non-overlapping, inclusive intervals
{
  intervals.sort((interval_1, interval_2) => interval_1[0] - interval_2[0])
  let output = []
  for (let interval of intervals) {
    // Case [i, i]:
    if (i == interval[0] && i == interval[1]) {
      continue;
    }
    // Case [j, k] and i < j or k < i
    if (i < interval[0] || interval[1] < i) {
      output.push(interval);
      continue;
    }
    // Case [i, k]: we have k != i so i < k so i+1 <=k
    if (i == interval[0]) {
      output.push([i + 1, interval[1]]);
      continue;
    }
    // Case [j, i]: we have j != i so j < i so j <= i-1
    if (i == interval[1]) {
      output.push([interval[0], i - 1]);
      continue;
    }
    // Otherwise we are "strictly inside":
    output.push([interval[0], i - 1]);
    output.push([i + 1, interval[1]])
  }
  return output;
}

const IDENT_BEGIN = [["a".charCodeAt(0), "z".charCodeAt(0)], ["A".charCodeAt(0), "Z".charCodeAt(0)],
["_".charCodeAt(0), "_".charCodeAt(0)]];
const IDENT_INSIDE = [["a".charCodeAt(0), "z".charCodeAt(0)], ["A".charCodeAt(0), "Z".charCodeAt(0)],
["_".charCodeAt(0), "_".charCodeAt(0)], ["0".charCodeAt(0), "9".charCodeAt(0)]];

function character_class_without(intervals, characters) {
  characters.sort((c) => c.charCodeAt(0));
  for (let character of characters) {
    intervals = intervals_exclude(intervals, character.charCodeAt(0));
  }
  intervals.sort((i1, i2) => i1[0] - i2[0]);
  let re_str = "";
  for (let interval of intervals) {
    let lchar = String.fromCharCode([interval[0]]);
    let rchar = String.fromCharCode([interval[1]]);
    re_str = `${re_str}${lchar}-${rchar}`;
  }
  return `[${re_str}]`
}

function add_to_trie(trie, element) {
  while (element != "") {
    if (element[0] in trie) {
      trie = trie[element[0]];
      element = element.substr(1);
    } else {
      trie[element[0]] = new Object();
      trie = trie[element[0]];
      element = element.substr(1);
    }
  }
  Object.defineProperty(trie, 'end', { value: true, writable: true })
}

function make_trie(strings) {
  let trie = new Object();
  for (let string of strings) {
    let old_trie = trie;
    add_to_trie(trie, string);
    trie = old_trie;
  }
  return trie
}

function* negate_keywords_trie(begin, trie) {
  let chars = Object.keys(trie);
  if (chars.length > 0 && begin) {
    yield character_class_without(IDENT_BEGIN, chars) + "[a-zA-Z0-9_]*"
  } else {
    yield character_class_without(IDENT_INSIDE, chars) + "[a-zA-Z0-9_]*"
  }
  for (let char of chars) {
    for (let negated of (negate_keywords_trie(false, trie[char]))) {
      yield char + negated
    }
  }
  if (chars.length == 0) {
    if (begin) {
      yield "[A-Za-z_][A-Za-z0-9_]*"
    } else {
      yield "[A-Za-z0-9_]+"
    }
  }
}

function negate_keywords_and_prefixes(keywords) {
  let trie = make_trie(keywords);
  let output = [];
  for (let negated_regexp of negate_keywords_trie(true, trie)) {
    output.push(negated_regexp);
  }
  return output.join("|");
}

function keyword_prefixes(trie) {
  let queue = [];
  for (let char of Object.keys(trie)) {
    queue.push([[""], char, trie[char]]);
  }
  let index = 0;
  let output = [];
  while (index < queue.length) {
    let prefixes, found_on, trie;
    [prefixes, found_on, trie] = queue[index];
    prefixes = Array.from(prefixes);
    if (Object.keys(trie).length > 0) {
      for (let index in prefixes) {
        prefixes[index] = prefixes[index] + found_on;
      }
      if (!('end' in trie)) {
        output = output.concat(prefixes);
      }
      for (let char of Object.keys(trie)) {
        queue.push([prefixes, char, trie[char]])
      }
    }
    index += 1;
  }
  return output.filter((x) => x.length > 0).join("|")
}

function negation(keywords) {
  return new RegExp([negate_keywords_and_prefixes(keywords), keyword_prefixes(make_trie(keywords))].join("|"))
}

const keywords = {
  "field": ["field"],
  "pred": ["pred"],
  "lcurly": ["{"],
  "rcurly": ["}"],
  "quantifier": ["forall", "exists"],
  "boolean_literal": ["false", "true"],
  "binop": ["==>", "<=>", "=", "==", "!=", "<=", ">=", "<", ">", "||", "&&", "in", "!in", "::", "**", "/", "*", "%", "*", "%", "++", "+", "--", "-"],
  "unop": ["!"],
  "proc": ["proc"],
  "requires": ["requires"],
  "ensures": ["ensures"],
  "if": ["if"],
  "else": ["else"],
  "fold": ["fold"],
  "unfold": ["unfold"],
  "var": ["var"],
  "assert": ["assert"],
  "assume": ["assume"],
  "havoc": ["havoc"],
  "while": ["while"],
  "invariant": ["invariant"],
  "coloneq": [":="],
  "eq": ["="],
  "returns": ["returns"],
  "return": ["return"],
  "val": ["val"],
  ";": [";"],
  ",": [","],
  ".": ["."],
  "?": ["?"],
  ":|": [":|"],
  "lcurly": ["{"],
  "rcurly": ["}"],
  "lparen": ["("],
  "rparen": [")"],
  "with": ["with"],
  "import": ["import"],
  "colon": ["colon", ":"],
  "coloncolon": ["::"],
  "modifier": ["implicit", "ghost"],
  "include": ["include"],
  "interface": ["interface"],
  "module": ["module"],
  "lemma": ["lemma"],
  "auto": ["auto"],
  "axiom": ["axiom"],
  "func": ["func"],
  "rep": ["rep"],
  "type": ["type"],
  "data": ["data"],
  "case": ["case"],
  "lmap_literal": ["{|"],
  "rmap_literal": ["|}"],
  "qmark": ["?"]
}

const all_keywords = Object.keys(keywords).map((k) => keywords[k]).reduce((x, y) => x.concat(y), []);

const all_colliding_keywords = all_keywords.filter((x) => x.match(/^[A-Za-z0-9_]*$/));

const IDENTIFIER = token(negation(all_colliding_keywords));

function into_tokens(keyword) {
  return choice.apply(null, keywords[keyword].map(token));
}

/* keywords */
const IMPORT = into_tokens("import");
const COLON = into_tokens("colon")
const COLONCOLON = into_tokens("coloncolon")
const LCURLY = into_tokens("lcurly");
const RCURLY = into_tokens("rcurly");
const VAL = into_tokens("val");
const FIELD = into_tokens("field");
const PRED = into_tokens("pred");
const PROC = into_tokens("proc");
const REQUIRES = into_tokens("requires");
const ENSURES = into_tokens("ensures");
const RETURNS = into_tokens("returns");
const RETURN = into_tokens("return");
const COLONEQ = into_tokens("coloneq");
const ASSERT = into_tokens("assert");
const WITH = into_tokens("with");
const ASSUME = into_tokens("assume");
const HAVOC = into_tokens("havoc");
const IF = into_tokens("if");
const ELSE = into_tokens("else");
const WHILE = into_tokens("while");
const INVARIANT = into_tokens("invariant");
const FOLD = into_tokens("fold");
const UNFOLD = into_tokens("unfold");
const VAR = into_tokens("var");
const BOOLEAN_LIT = into_tokens("boolean_literal");
const UNOP = into_tokens("unop");
const BINOP = into_tokens("binop");
const QUANTIFIER = into_tokens("quantifier");
const MODIFIER = into_tokens("modifier");
const INCLUDE = into_tokens("include");
const INTERFACE = into_tokens("interface");
const MODULE = into_tokens("module");
const LEMMA = into_tokens("lemma");
const AUTO = into_tokens("auto");
const AXIOM = into_tokens("axiom");
const FUNC = into_tokens("func");
const REP = into_tokens("rep");
const TYPE = into_tokens("type");
const DATA = into_tokens("data");
const CASE = into_tokens("case");
const LMAP_LITERAL = into_tokens("lmap_literal");
const RMAP_LITERAL = into_tokens("rmap_literal");
const LPAREN = into_tokens("lparen");
const RPAREN = into_tokens("rparen");
const QMARK = into_tokens("qmark");

/* constants */
const SEPERATOR = choice(token(","), token(";"))
const END_STMT = token(";");
const DOT = token(".")
const EQ = token("=");

module.exports = grammar({
  name: "raven",

  extras: ($) => [/(\s|\f)/, $.comment, $.block_comment], // Ignore whitespace, comments

  rules: {
    source_file: ($) => seq(repeat($.include_stmt), repeat($.defn)),
    // A borrow from Java:
    double_quote_string: ($) => seq(
      '"',
      repeat(choice(
        $.string_fragment,
        $.escape_sequence,
      )),
      '"',
    ),
    single_quote_string: ($) => seq(
      "'",
      repeat(choice(
        $.string_fragment,
        $.escape_sequence,
      )),
      "'",
    ),
    string_fragment: (_) => token.immediate(prec(1, /[^"\\]+/)),
    escape_sequence: (_) => token.immediate(seq(
      '\\',
      choice(
        /[^xu0-7]/,
        /[0-7]{1,3}/,
        /x[0-9a-fA-F]{2}/,
        /u[0-9a-fA-F]{4}/,
        /u\{[0-9a-fA-F]+\}/,
      ))),
    include_stmt: ($) => seq($.kwd_include, $.string),
    import_stmt: ($) => seq($.kwd_import, $.identifier),
    string: ($) => choice($.double_quote_string, $.single_quote_string),
    defn: ($) => choice($.rep_defn, $.func_defn, $.axiom_defn, $.pred_defn, $.lemma_defn, $.proc_defn, $.field_defn, $.val_defn, $.interface_defn, $.import_stmt, $.module_defn),
    interface_body: ($) => seq($.lcurly, repeat($.defn), $.rcurly),
    rep_defn: ($) => seq($.kwd_rep, $.kwd_type, field("name", $.identifier), optional(seq(choice($.eq, $.coloneq), field("data", $.data_defn)))),
    lcurly: ($) => LCURLY,
    rcurly: ($) => RCURLY,
    data_defn: ($) => seq($.kwd_data, $.lcurly, optional(field("body", $.data_body)), $.rcurly),
    data_body: ($) => seq(repeat((seq(field("cases", $.case_defn), $.end_stmt))), field("case", $.case_defn)),
    case_defn: ($) => seq($.kwd_case, field("name", $.identifier), field("parameters", optional($.arglist))),
    interface_defn: ($) =>
      seq($.kwd_interface,
        field("name", $.identifier),
        field("parameters", optional($.type_cons)),
        field("typecons", optional(seq($.colon, $.type))),
        field("body", $.interface_body)),
    module_defn: ($) =>
      seq($.kwd_module,
        field("name", $.identifier),
        field("parameters", optional($.type_cons)),
        field("typecons", optional(seq($.colon, $.type))),
        field("body", $.interface_body)),
    func_defn: ($) =>
      seq($.kwd_func,
        field("name", $.identifier),
        field("parameters", $.arglist),
        field("returns", $.returns_clause),
        field("body", optional($.proc_body))),
    axiom_defn: ($) =>
      seq(optional($.kwd_auto),
        $.kwd_axiom,
        field("name", $.identifier),
        field("parameters", $.arglist),
        field("io", repeat($.io_spec_clause))),
    lemma_defn: ($) =>
      seq(optional($.kwd_auto),
        $.kwd_lemma,
        field("name", $.identifier),
        field("parameters", $.arglist),
        field("io", repeat($.io_spec_clause)),
        field("body", $.proc_body)),
    pred_defn: ($) =>
      seq($.kwd_pred,
        field("name", $.identifier),
        field("parameters", $.arglist),
        optional(field("body", $.pred_body))),
    proc_defn: ($) =>
      seq($.kwd_proc,
        field("name", $.identifier),
        field("parameters", $.arglist),
        repeat(choice(field("io", $.io_spec_clause),
          field("returns", $.returns_clause))),
        optional(field("body", $.proc_body))),
    type_con: ($) => seq($.identifier, token(":"), $.identifier),
    type_cons: ($) => seq(token("["), repeat($.type_con), token("]")),
    val_defn: ($) => seq(repeat($.kwd_modifier), $.kwd_val, $.arg, optional(seq(choice($.coloneq, $.eq), $.expr))),
    field_defn: ($) => seq($.kwd_field, $.arg),
    io_spec_clause: ($) => choice(seq($.kwd_requires, $.expr), seq($.kwd_ensures, $.expr)),
    returns_clause: ($) => seq($.kwd_returns, field("arglist", $.arglist)),
    stmt: ($) => choice($.stmt_syntax, $.call),
    proc_body: ($) => choice(seq($.lcurly, repeat(seq($.stmt, optional($.end_stmt))), $.rcurly), $.stmt),
    stmt_syntax: ($) => prec.dynamic(20, choice($.if_stmt, $.while_stmt, $.fold_stmt, $.unfold_stmt, $.var_dec, $.assert_stmt, $.assume_stmt, $.havoc_stmt, $.val_defn, $.assign_stmt, $.return_stmt)),
    call: ($) => prec.dynamic(19, seq($.expr)),
    return_stmt: ($) => seq($.kwd_return, optional(seq(repeat(seq($.expr, $.seperator)), $.expr))),
    assign_stmt: ($) => seq(repeat($.kwd_modifier), repeat(seq(field("lhs", $.location), $.seperator)), $.location, $.coloneq, field("rhs", $.expr)),
    assert_stmt: ($) => seq($.kwd_assert, $.expr, optional($.with_stmt)),
    with_stmt: ($) => seq($.kwd_with, $.proc_body),
    assume_stmt: ($) => seq($.kwd_assume, $.expr),
    havoc_stmt: ($) => seq($.kwd_havoc, $.expr),
    if_stmt: ($) => seq($.kwd_if, $.paren_expr, $.proc_body, repeat($.elif_clause), optional($.else_clause)),
    elif_clause: ($) => seq($.kwd_else, $.kwd_if, $.paren_expr, $.proc_body),
    else_clause: ($) => seq($.kwd_else, $.proc_body),
    while_stmt: ($) => seq($.kwd_while, optional($.paren_expr), repeat($.invariant_spec_clause), $.proc_body),
    invariant_spec_clause: ($) => seq($.kwd_invariant, $.expr),
    fold_stmt: ($) => seq($.kwd_fold, $.expr),
    unfold_stmt: ($) => seq($.kwd_unfold, $.expr),
    var_dec: ($) => seq(repeat($.kwd_modifier), $.kwd_var, $.arg, optional(seq(choice($.coloneq, $.eq), $.expr))),
    arglist: ($) => seq($.lparen, repeat(seq(field("params", $.arg), $.seperator)), field("param", optional($.arg)), $.rparen),
    arg: ($) => seq(repeat($.kwd_modifier), field("varname", $.identifier), $.colon, field("vartype", $.type)),
    type: ($) => choice(field("ty_name", $.identifier), field("ty_app", $.type_application)),
    type_application: ($) => seq(field("ty_name", $.identifier), token("["), $.typelist, token("]")),
    typelist: ($) => seq(repeat(seq($.type, $.seperator)), $.type),
    pred_body: ($) => seq($.lcurly, $.expr, $.rcurly),
    expr: ($) => choice($.value, $.unop, $.binop, $.ternary_op, $.quantified_expr, $.paren_expr, $.apply, $.update, $.lookup, $.map_literal),
    map_literal_l: (_) => LMAP_LITERAL,
    map_literal_r: (_) => RMAP_LITERAL,
    map_literal: ($) => seq($.map_literal_l, choice($.map_literal_id, $.map_literal_expr), $.map_literal_r),
    map_literal_id: ($) => seq($.identifier, optional(seq($.colon, $.type))),
    map_literal_expr: ($) => $.expr,
    update: ($) => prec(8, seq($.expr, token("["), $.expr, $.coloneq, $.expr, token("]"))),
    apply: ($) => prec(10, seq(field("callee", $.expr), $.lparen, repeat(seq($.expr, $.seperator)), optional($.expr), $.rparen)),
    lookup: ($) => prec(9, seq($.expr, token("["), repeat(seq($.expr, $.seperator)), optional($.expr), token("]"))),
    paren_expr: ($) => prec(3, seq($.lparen, $.expr, $.rparen)),
    value: ($) => choice($.number, $.boolean_lit, $.location),
    boolean_lit: ($) => BOOLEAN_LIT,
    number: ($) => seq(optional(token("-")), /\d+|\d*\.\d+/),
    unop: ($) => prec(2, seq($.unop_op, $.expr)),
    unop_op: ($) => UNOP,
    binop: ($) => prec.left(1, seq($.expr, $.binop_op, $.expr)),
    binop_op: ($) => BINOP,
    ternary_op: ($) => prec.left(1, seq($.expr, $.qmark, $.expr, $.ternary_colon, $.expr)),
    quantified_expr: ($) => prec(7, seq($.kwd_quantifier, seq($.arg, repeat(seq(", ", $.arg))), $.coloncolon, optional($.trigger), $.expr)),
    trigger_begin: ($) => LCURLY,
    trigger_end: ($) => RCURLY,
    trigger: ($) => seq($.trigger_begin, repeat(seq($.expr, $.seperator)), $.expr, $.trigger_end),
    location: ($) => seq(repeat(seq($.expr, $.dot)), field("name_or_field", $.identifier)),
    identifier: ($) => prec.left(100, seq(IDENTIFIER, repeat(seq($.dot, IDENTIFIER)))),
    /* CONSTANTS */
    lparen: ($) => LPAREN,
    rparen: ($) => RPAREN,
    lmap_literal: ($) => LMAP_LITERAL,
    rmap_literal: ($) => RMAP_LITERAL,
    ternary_colon: ($) => $.colon,
    colon: ($) => COLON,
    coloncolon: ($) => COLONCOLON,
    seperator: ($) => SEPERATOR,
    qmark: ($) => QMARK,
    dot: ($) => DOT,
    coloneq: ($) => COLONEQ,
    eq: ($) => EQ,
    end_stmt: ($) => END_STMT,
    /* KEYWORDS */
    kwd_import: ($) => IMPORT,
    kwd_field: ($) => FIELD,
    kwd_pred: ($) => PRED,
    kwd_proc: ($) => PROC,
    kwd_requires: ($) => REQUIRES,
    kwd_ensures: ($) => ENSURES,
    kwd_returns: ($) => RETURNS,
    kwd_return: ($) => RETURN,
    kwd_assert: ($) => ASSERT,
    kwd_assume: ($) => ASSUME,
    kwd_havoc: ($) => HAVOC,
    kwd_with: ($) => WITH,
    kwd_val: ($) => VAL,
    kwd_if: ($) => IF,
    kwd_else: ($) => ELSE,
    kwd_while: ($) => WHILE,
    kwd_invariant: ($) => INVARIANT,
    kwd_fold: ($) => FOLD,
    kwd_unfold: ($) => UNFOLD,
    kwd_var: ($) => VAR,
    kwd_quantifier: ($) => QUANTIFIER,
    kwd_modifier: ($) => MODIFIER,
    kwd_include: ($) => INCLUDE,
    kwd_interface: ($) => INTERFACE,
    kwd_module: ($) => MODULE,
    kwd_rep: ($) => REP,
    kwd_type: ($) => TYPE,
    kwd_data: ($) => DATA,
    kwd_case: ($) => CASE,
    kwd_auto: ($) => AUTO,
    kwd_lemma: ($) => LEMMA,
    kwd_axiom: ($) => AXIOM,
    kwd_func: ($) => FUNC,
    /* COMMENTS */
    // borrowing from the C99 parser
    block_comment: ($) => seq(
      "/*",
      optional($.comment_text),
      "*/"
    ),
    comment_text: $ => repeat1(choice(/.|\n|\r/)),
    comment: _ => seq('//', /(\\+(.|\r?\n)|[^\\\n])*/),
  },
  conflicts: ($) => [[$.location], [$.proc_defn], [$.func_defn], [$.return_stmt], [$.while_stmt, $.expr], [$.if_stmt, $.elif_clause], [$.if_stmt], [$.assign_stmt, $.var_dec, $.val_defn, $.call], [$.assign_stmt, $.value], [$.map_literal_id, $.location]],
});

const AU = token("au");
const ATOMIC = token("atomic");
const ATOMICTOKEN = token("AtomicToken");
const BOOL = token("Bool");
const CAS = token("cas");
const CLOSEINV = token("closeInv");
const EXHALE = token("exhale");
const INT = token("Int");
const INHALE = token("inhale");
const INV = token("inv");
const MAP = token("Map");
const NEW = token("new");
const NULL = token("null");
const OPENINV = token("openInv");
const OWN = token("own");
const PERM = token("Perm");
const REF = token("Ref");
const REAL = token("Real");
const SUBSETEQ = token("subseteq");
const SET = token("Set");
