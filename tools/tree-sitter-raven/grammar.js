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

const IDENT_BEGIN = [["a".charCodeAt(0), "z".charCodeAt(0)], ["_".charCodeAt(0), "_".charCodeAt(0)]];
const MOD_IDENT_BEGIN = [["A".charCodeAt(0), "Z".charCodeAt(0)], ["_".charCodeAt(0), "_".charCodeAt(0)]];
const IDENT_INSIDE = [["a".charCodeAt(0), "z".charCodeAt(0)], ["A".charCodeAt(0), "Z".charCodeAt(0)],
["_".charCodeAt(0), "_".charCodeAt(0)], ["0".charCodeAt(0), "9".charCodeAt(0)], ['\\'.charCodeAt(0), '\\'.charCodeAt(0)]];

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

function* negate_keywords_trie(begin, is_module, trie) {
  let chars = Object.keys(trie);
  if (chars.length > 0 && begin && is_module) {
    yield character_class_without(MOD_IDENT_BEGIN, chars) + "[a-zA-Z0-9_]*"
  } else if (chars.length > 0 && begin) {
    yield character_class_without(IDENT_BEGIN, chars) + "[a-zA-Z0-9_]*"
  } else {
    yield character_class_without(IDENT_INSIDE, chars) + "[a-zA-Z0-9_]*"
  }
  for (let char of chars) {
    for (let negated of (negate_keywords_trie(false, is_module, trie[char]))) {
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

function negate_keywords_and_prefixes(keywords, is_module) {
  let trie = make_trie(keywords);
  let output = [];
  for (let negated_regexp of negate_keywords_trie(true, is_module, trie)) {
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

function negation(keywords, is_module) {
  return new RegExp([negate_keywords_and_prefixes(keywords, is_module), keyword_prefixes(make_trie(keywords))].join("|"))
}

const keywords = {
  kwd_spec: ["assert", "assume", "exhale", "inhale", "fold", "unfold"],
  kwd_inv: ["closeInv", "openInv", "inv"],
  kwd_au: ["au"],
  kwd_atomic: ["atomic"],
  kwd_axiom: ["axiom"],
  kwd_atomic_token: ["AtomicToken"],
  kwd_auto: ["auto"],
  kwd_bool: ["Bool"],
  kwd_cas: ["cas"],
  kwd_case: ["case"],
  kwd_data: ["data"],
  kwd_else: ["else"],
  kwd_ensures: ["ensures"],
  kwd_quantifier: ["forall", "exists"],
  kwd_const: ["false", "true", "null"],
  kwd_field: ["field"],
  kwd_func: ["func", "pred"],
  kwd_ghost: ["ghost"],
  kwd_havoc: ["havoc"],
  kwd_if: ["if"],
  kwd_int: ["Int"],
  kwd_include: ["include"],
  kwd_module: ["interface", "module"],
  kwd_invariant: ["invariant"],
  kwd_import: ["import"],
  kwd_implicit: ["implicit"],
  kwd_lemma: ["lemma"],
  kwd_rep: ["rep"],
  kwd_map: ["Map"],
  kwd_new: ["new"],
  kwd_own: ["own"],
  kwd_perm: ["Perm"],
  kwd_proc: ["proc"],
  kwd_ref: ["Ref"],
  kwd_real: ["Real"],
  kwd_requires: ["requires"],
  kwd_return: ["return"],
  kwd_returns: ["returns"],
  kwd_set: ["Set"],
  kwd_type: ["type"],
  kwd_var: ["val", "val"],
  kwd_with: ["with"],
  kwd_while: ["while"],
  /* hack: keywords contains "in" to exclude "in" from identifiers */
  kwd_in: ["in"],
}

const delimeters = {
  delim_lbracepipe: ["{|"],
  delim_rbracepipe: ["|}"],
  delim_lbracketpipe: ["[|"],
  delim_rbracketpipe: ["|]"],
  delim_lparen: ['('],
  delim_rparen: [')'],
  delim_lbrace: ['{'],
  delim_rbrace: ['}'],
  delim_lbracket: ['['],
  delim_rbracket: [']'],
  delim_lghostbrace: ["{!"],
  delim_rghostbrace: ["!}"],
}

const operators = {
  op_implies: ["==>"],
  op_iff: ["<=>"],
  op_eq: ["="],
  op_eqeq: ["=="],
  op_neq: ["!="],
  op_leq: ["<="],
  op_geq: [">="],
  op_lt: ["<"],
  op_gt: [">"],
  op_or: ["||"],
  op_and: ["&&"],
  op_in: ["in"],
  op_not_in: ["!in"],
  op_not: ["!"],
  op_union: ["++"],
  op_diff: ["--"],
  op_multop_inter: ["**"],
  op_plus: ["+"],
  op_minus: ["-"],
  op_div: ["/"],
  op_mul: ["*"],
  op_mod: ["%"],
  op_coloneq: [":="],
  op_coloncolon: ["::"],
  op_colon: [":"],
  op_semicolon: [";"],
  op_comma: [","],
  op_dot: ["."],
  op_qmark: ["?"],
  op_colonpipe: [":|"],
}

/*** LexerRules(Rules) is a class extending the class "Rules" with
     lexer rules and data. ***/
const LexerRules = (Rules) => class AllRules extends Rules {
  constructor() {
    super();
    for (let kwd of Object.keys(keywords)) {
      this[kwd] = _ => into_tokens(keywords, kwd);
    }
    for (let delim of Object.keys(delimeters)) {
      this[delim] = _ => into_tokens(delimeters, delim);
    }
    for (let op of Object.keys(operators)) {
      this[op] = _ => into_tokens(operators, op);
    }
  }

  identifier = _ => IDENTIFIER;
  mod_identifier = _ => MOD_IDENTIFIER;
  block_comment = ($) => seq("/*", optional($.comment_text), "*/");
  comment_text = _ => repeat1(choice(/.|\n|\r/));
  comment = _ => seq('//', /(\\+(.|\r?\n)|[^\\\n])*/);
  double_quote_string = ($) => seq(
    '"',
    repeat(choice(
      $.string_fragment,
      $.escape_sequence,
    )),
    '"',
  );
  single_quote_string = ($) => seq(
    "'",
    repeat(choice(
      $.string_fragment,
      $.escape_sequence,
    )),
    "'",
  );
  string_fragment = _ => token.immediate(prec(1, /[^"\\]+/));
  escape_sequence = _ =>
    token.immediate(seq('\\',
      choice(
        /[^xu0-7]/,
        /[0-7]{1,3}/,
        /x[0-9a-fA-F]{2}/,
        /u[0-9a-fA-F]{4}/,
        /u\{[0-9a-fA-F]+\}/,
      )));
  string = ($) => choice($.double_quote_string, $.single_quote_string);
}


function into_tokens(arr, keyword) {
  return choice.apply(null, (arr[keyword]).map(token));
}

const all_keywords = Object.keys(keywords).map((k) => keywords[k]).reduce((x, y) => x.concat(y), []);

const all_colliding_keywords = all_keywords.filter((x) => x.match(/^[A-Za-z0-9_]*$/));

const IDENTIFIER = token(negation(all_colliding_keywords, false));

const MOD_IDENTIFIER = token(negation(all_colliding_keywords, true));


function separated_nonempty_list(nonterminal, sep, name) {
  return seq(repeat(seq(field(name, nonterminal), sep)), field(name, nonterminal));
}

function separated_list(nonterminal, sep, name) {
  return seq(repeat(seq(field(name, nonterminal), sep)), optional(field(name, nonterminal)));
}

function member_def_list($) {
  return field("member_def_list", repeat(seq(field("ms", $.member_def), optional($.op_semicolon))))
}

function expr_list($) {
  return field("expr_list", separated_list($.op_comma, $.expr, "expr"))
}

/***
    toplevel definitions, block, and statement syntax
***/
class SyntaxRules {
  source_file = ($) => seq(repeat(field("files", $.include_stmt)), member_def_list($));
  include_stmt = ($) => seq($.kwd_include, $.string);
  member_def = ($) => choice($.field_def, $.module_def, $.type_def, $.var_def, $.proc_def, $.func_def, $.import_dir);
  field_def = ($) => seq(optional(field("modifier", $.ghost_modifier)), $.kwd_field, $.identifier, $.op_colon, $.type_expr);
  ghost_modifier = ($) => $.kwd_ghost;
  module_def = ($) =>
    seq(field("interface", $.kwd_module),
      $.module_header,
      optional(choice($.module_inst, $.module_impl)));
  module_header = ($) => seq($.mod_identifier, optional($.module_param_list), optional($.return_type));
  module_param_list = ($) => seq($.delim_lbracket, separated_list($.module_param, $.op_comma, "module_parameter"), $.delim_rbracket);
  module_param = ($) => seq(field("inst_name", $.identifier), $.op_colon, field("inst_type", $.type_expr));
  return_type = ($) => seq($.op_colon, $.identifier);
  module_inst = ($) => seq($.delim_lbrace, member_def_list($), $.delim_rbrace);
  module_impl = ($) => seq($.mod_identifier, optional($.module_inst_args));
  module_inst_args = ($) => seq($.delim_lbracket, separated_list($.mod_identifier, $.op_comma, "id"), $.delim_rbracket);
  type_def = ($) => seq($.type_decl, optional(seq($.op_eq, $.type_def_expr)));
  type_decl = ($) => seq(optional($.type_mod), $.kwd_type, $.mod_identifier);
  type_mod = ($) => $.kwd_rep;
  type_def_expr = ($) => choice($.type_expr, $.data_expr);
  data_expr = ($) => seq($.kwd_data, $.delim_lbrace, separated_list($.case_defn, $.op_semicolon, "case"), $.delim_rbrace);
  case_defn = ($) => seq($.kwd_case, field("name", $.identifier), field("parameters", optional($.variant_args)));
  variant_args = ($) => seq($.delim_lparen, separated_list($.bound_var, $.op_comma, "arg"), $.delim_rparen);
  bound_var = ($) => seq($.identifier, $.op_colon, $.type_expr);
  type_expr = ($) => choice($.kwd_int, $.kwd_real, $.kwd_bool, $.kwd_ref, $.kwd_perm, $.kwd_atomic_token, $.kwd_set, $.type_expr_map, $.mod_identifier, $.type_expr_list, $.type_expr_app);
  type_expr_map = ($) => seq($.kwd_map, $.delim_lbracket, $.type_expr, $.op_comma, $.type_expr, $.delim_rbracket);
  type_expr_list = ($) => seq($.delim_lparen, separated_nonempty_list($.type_expr, $.op_comma, "type"), $.delim_rparen);
  type_expr_app = ($) => seq(field("caller", $.type_expr), $.delim_lbracket, separated_list($.type_expr, $.op_comma, "arg"), $.delim_rbracket);
  var_def = ($) =>
    choice(seq($.ghost_modifier, $.kwd_var, optional($.bound_var_type), optional(seq($.op_eq, $.expr))),
      seq($.ghost_modifier, $.kwd_var, optional($.bound_var_type), $.op_coloneq, $.expr));
  proc_def = ($) => seq($.proc_kind, $.proc_decl, optional($.block));
  proc_kind = ($) => choice($.kwd_proc, seq(optional($.kwd_auto), $.kwd_lemma), seq(optional($.kwd_auto), $.kwd_axiom));
  proc_decl = ($) => $.callable_decl;
  callable_decl = ($) => seq($.identifier, $.delim_lparen, optional($.var_decls_with_modifiers), $.delim_rparen, optional($.returns_clause), repeat($.contract));
  var_decls_with_modifiers = ($) => separated_nonempty_list(seq(repeat($.var_modifier), $.bound_var), $.op_comma, "arg");
  var_modifier = ($) => choice($.kwd_implicit, $.kwd_ghost);
  returns_clause = ($) => seq($.kwd_returns, $.delim_lparen, optional($.var_decls_with_modifiers), $.delim_rparen);
  contract = ($) => seq(repeat($.contract_modifier), choice($.kwd_requires, $.kwd_ensures), $.expr);
  contract_modifier = ($) => $.kwd_atomic;
  bound_var_type = ($) => choice($.identifier, seq($.identifier, $.op_colon, $.type_expr));
  block = ($) => seq($.delim_lbrace, optional($.stmt_list), $.delim_rbrace);
  stmt_list = ($) => repeat1($.stmt);
  stmt = ($) => $.stmt_desc;
  stmt_desc = ($) =>
    choice($.stmt_wo_trailing_substmt,
      $.if_then_stmt,
      $.if_then_else_stmt,
      $.while_stmt,
      $.ghost_block);
  stmt_wo_trailing_substmt = ($) =>
    choice(seq($.var_def, $.op_semicolon),
      $.block,
      seq($.call_expr, $.op_semicolon),
      $.assign_stmt,
      $.bind_stmt,
      $.havoc_stmt,
      $.spec_stmt,
      $.return_stmt,
      $.resource_stmt);
  assign_stmt = ($) => seq(separated_nonempty_list($.expr, $.op_comma, "lhs_proj"), $.op_coloneq, choice($.new_expr, $.expr), $.op_semicolon);
  bind_stmt = ($) => seq(separated_nonempty_list($.expr, $.op_comma, "lhs_proj"), $.op_colonpipe, $.expr, $.op_semicolon);
  havoc_stmt = ($) => seq($.kwd_havoc, $.qual_ident, $.op_semicolon);
  with_clause = ($) => choice($.op_semicolon, seq($.kwd_with, $.block));
  spec_stmt = ($) => seq($.kwd_spec, $.expr, $.with_clause);
  return_stmt = ($) => seq($.kwd_return, separated_list($.expr, $.op_comma, "expr"), $.op_semicolon);
  resource_stmt = ($) => seq($.kwd_inv, $.qual_ident, $.delim_lparen, separated_list($.expr, $.op_comma, "expr"), $.delim_rparen, $.op_semicolon);
  new_expr = ($) => seq($.kwd_new, $.delim_lparen, separated_list(seq($.qual_ident, $.op_colon, $.expr), $.op_comma, "rhs_proj"));
  call_expr = ($) => seq($.qual_ident_expr, $.call);
  if_then_stmt = ($) => seq($.kwd_if, $.delim_lparen, $.expr, $.delim_rparen, $.stmt);
  if_then_else_stmt = ($) => seq($.kwd_if, $.delim_lparen, $.expr, $.delim_rparen, $.stmt_no_short_if, $.kwd_else, $.stmt);
  stmt_no_short_if = ($) => $.stmt_no_short_if_desc;
  stmt_no_short_if_desc = ($) => choice($.stmt_wo_trailing_substmt, $.if_then_else_stmt_no_short_if, $.while_stmt_no_short_if);
  if_then_else_stmt_no_short_if = ($) => seq($.kwd_if, $.delim_lparen, $.expr, $.delim_rparen, $.stmt_no_short_if, $.kwd_else, $.stmt_no_short_if);
  while_stmt_no_short_if = ($) => choice(seq($.kwd_while, $.delim_lparen, $.expr, $.delim_rparen, $.stmt_no_short_if));
  while_stmt = ($) => choice(seq($.kwd_while, $.delim_lparen, $.expr, $.delim_rparen, repeat1($.loop_contract), $.block), seq($.kwd_while, $.delim_lparen, $.expr, $.delim_rparen, $.stmt));
  loop_contract = ($) => seq($.kwd_invariant, $.expr);
  ghost_block = ($) => seq($.delim_lghostbrace, optional($.stmt_list), $.delim_rghostbrace);
  func_def = ($) => seq($.func_decl, optional(seq($.delim_lbrace, $.expr, $.delim_rbrace)));
  func_decl = ($) => choice(seq($.kwd_func, $.callable_decl), seq($.kwd_func, $.callable_decl_out_vars));
  callable_decl_out_vars = ($) => seq($.identifier, $.delim_lparen, optional($.var_decls_with_modifiers), $.op_semicolon, optional($.var_decls_with_modifiers), $.delim_rparen, repeat($.contract));
  import_dir = ($) => prec.left(choice(seq($.kwd_import, $.qual_ident), seq($.kwd_import, $.mod_identifier)));
}

const expr_parsers = {
  expr: ($) => prec.right(choice($.tuple_expr, $._expr_with_quantifiers)),
  tuple_expr: ($) => prec.right(seq($.delim_lparen, separated_nonempty_list($.expr, $.op_comma, "proj"), $.delim_rparen)),
  _expr_with_quantifiers: ($) => prec.right(choice($.quantified_expr, $._expr_with_ternaries)),
  quantified_expr: ($) => seq($.kwd_quantifier, separated_list($.bound_var, $.op_comma, "variable", true), $.op_coloncolon, repeat($.trigger), $.expr),
  _expr_with_ternaries: ($) => prec.right(choice($.ternary_expr, $._expr_with_iffs)),
  ternary_expr: ($) => seq($._expr_with_iffs, $.op_qmark, $.expr, $.op_colon, $.expr),
  trigger: ($) => seq($.delim_lbrace, expr_list($), $.delim_rbrace),
  _expr_with_iffs: ($) => prec.right(choice($.iff_expr, $._expr_with_impls)),
  iff_expr: ($) => seq($.impl_expr, $.op_iff, $.expr),
  _expr_with_impls: ($) => prec.right(choice($.impl_expr, $.expr_with_ors)),
  impl_expr: ($) => seq($.expr_with_ors, $.op_implies, $.expr),
  expr_with_ors: ($) => prec.right(seq($.or_expr, $.expr_with_ands)),
  or_expr: ($) => seq($.expr_with_ands, $.op_or, $.expr),
  expr_with_ands: ($) => prec.right(choice($.and_expr, $.expr_with_eqs)),
  and_expr: ($) => seq($.expr_with_eqs, $.op_and, $.expr),
  expr_with_eqs: ($) => prec.right(choice($.eq_expr, $.expr_with_neqs)),
  eq_expr: ($) => seq($.expr_with_neqs, $.op_eq, $.expr),
  expr_with_neqs: ($) => prec.right(choice($.neq_expr, $.expr_with_ins)),
  neq_expr: ($) => seq($.expr_with_ins, $.op_neq, $.expr),
  expr_with_ins: ($) => prec.right(choice($.in_expr, $.expr_with_not_ins)),
  in_expr: ($) => seq($.expr_with_not_ins, $.op_in, $.parenthesized_value_expr),
  expr_with_not_ins: ($) => prec.right(choice($.not_in_expr, $.value_expr)),
  not_in_expr: ($) => seq($.value_expr, $.op_not_in, $.parenthesized_value_expr),
  parenthesized_value_expr: ($) =>
    choice(seq($.delim_lparen, $.value_expr, $.delim_rparen),
      $.value_expr),
  value_expr: ($) => prec.right(choice($.add_expr, $.expr_with_minus)),
  add_expr: ($) => seq($.expr_with_minus, $.op_plus, $.parenthesized_value_expr),
  expr_with_minus: ($) => prec.right(choice($.minus_expr, $.expr_with_mul)),
  minus_expr: ($) => seq($.expr_with_mul, $.op_minus, $.parenthesized_value_expr),
  expr_with_mul: ($) => prec.right(choice($.mul_expr, $.expr_with_div)),
  mul_expr: ($) => seq($.expr_with_div, $.op_mul, $.parenthesized_value_expr),
  expr_with_div: ($) => prec.right(choice($.div_expr, $.expr_with_negatives)),
  div_expr: ($) => seq($.expr_with_negatives, $.op_div, $.parenthesized_value_expr),
  expr_with_negatives: ($) => prec.right(choice($.negative_expr, $.expr_with_nots)),
  negative_expr: ($) => seq($.op_minus, $.parenthesized_value_expr),
  expr_with_nots: ($) => prec.right(choice($.not_expr, $.primary_expr)),
  not_expr: ($) => prec.right(seq($.op_not, $.primary_expr)),
  primary_expr: ($) => choice($.literal, $.map_and_updates, $.compr_expr, $.dot_expr, $.own_expr, $.cas_expr, $.au_expr, $.lookup_expr),
  literal: ($) => choice($.kwd_const, $.number),
  map_and_updates: ($) => seq($.delim_lparen, $.expr, $.delim_rparen, repeat($.map_update)),
  map_update: ($) => seq($.delim_lbracket, $.expr, $.op_coloneq, $.expr, $.delim_rbracket),
  compr_expr: ($) =>
    choice(seq($.delim_lbracepipe, /* expr_list($), */ $.delim_rbracepipe),
      seq($.delim_lbracepipe, $.op_coloncolon, $.expr, $.delim_rbracepipe),
      seq($.delim_lbracketpipe, $.bound_var, $.op_coloncolon, $.expr, $.delim_rbracketpipe)),
  dot_expr: ($) => prec.right(seq($.qual_ident_expr, optional($.call_opt))),
  qual_ident_expr: ($) => choice($.identifier, seq($.primary_expr, $.op_dot, $.identifier),
    seq($.primary_expr, $.delim_lparen, $.qual_ident, $.delim_rparen)),
  qual_ident: ($) => choice($.identifier, seq($.mod_identifier, $.identifier)),
  call_opt: ($) => choice(seq($.call, repeat($.map_update)), repeat1($.map_update)),
  call: ($) => seq($.delim_lparen, /* expr_list($), */ $.delim_rparen),
  own_expr: ($) => seq($.kwd_own, $.delim_lparen, expr_list($), $.delim_rparen),
  cas_expr: ($) => seq($.kwd_cas, $.delim_lparen, expr_list($), $.delim_rparen),
  au_expr: ($) => seq($.kwd_au, $.delim_lparen, $.qual_ident, expr_list($), $.delim_rparen),
  lookup_expr: ($) => choice(seq($.qual_ident_expr, $.lookup), seq($.delim_lparen, $.expr, $.delim_rparen, $.lookup)),
  lookup: ($) => choice(seq($.delim_lbracket, $.expr, $.delim_rbracket), $.hash),
  hash: ($) => $.integer,
  integer: _ => token(/[0-9]+/),
  float: _ => token(/[0-9]*.[0-9]+/),
  number: ($) => choice($.integer, $.float),
}

/***
    All non-lexical parsing rules including expressions
***/
class ParserRules extends SyntaxRules {
  constructor() {
    super();
    let length = Object.keys(expr_parsers).length + 1;
    for (const entry of Object.keys(expr_parsers).entries()) {
      this[entry[1]] = ($) => prec(entry[0], expr_parsers[entry[1]]($))
    }
  }
}

module.exports = grammar({
  name: "raven",

  extras: ($) => [/(\s|\f)/, $.comment, $.block_comment], // Ignore whitespace, comments

  rules: new (LexerRules(ParserRules)),
});
