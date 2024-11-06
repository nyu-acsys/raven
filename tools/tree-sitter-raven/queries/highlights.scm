[ (kwd_import)
  (kwd_field)
  (kwd_pred)
  (kwd_proc)
  (kwd_requires)
  (kwd_ensures)
  (kwd_returns)
  (kwd_return)
  (kwd_assert)
  (kwd_assume)
  (kwd_havoc)
  (kwd_with)
  (kwd_val)
  (kwd_if)
  (kwd_else)
  (kwd_while)
  (kwd_invariant)
  (kwd_fold)
  (kwd_unfold)
  (kwd_var)
  (kwd_quantifier)
  (kwd_modifier)
  (kwd_include)
  (kwd_interface)
  (kwd_module)
  (kwd_rep)
  (kwd_type)
  (kwd_auto)
  (kwd_case)
  (kwd_func)
  (kwd_lemma)
  (kwd_axiom)
  (kwd_data) ] @keyword
[ (binop) (unop) (ternary_op) ] @operator
(number) @number
(type ty_name: (identifier) @type)
(type ty_app: (type_application ty_name: (identifier) @type))
[ (block_comment)
  (comment_text)
  (comment) ] @comment
[
  "{"
  "}"
] @punctuation.bracket

[
  (boolean_lit)
] @constant.builtin


(func_defn name: (identifier) @function)
(func_defn parameters: (arglist params: (arg varname: (identifier) @variable.parameter)))
(func_defn parameters: (arglist param: (arg varname: (identifier) @variable.parameter)))
(func_defn returns: (returns_clause arglist: (arglist params: (arg varname: (identifier) @variable.parameter))))
(func_defn returns: (returns_clause arglist: (arglist param: (arg varname: (identifier) @variable.parameter))))
(string) @string

(proc_defn name: (identifier) @function)
(proc_defn parameters: (arglist params: (arg varname: (identifier) @variable.parameter)))
(proc_defn parameters: (arglist param: (arg varname: (identifier) @variable.parameter)))
(proc_defn returns: (returns_clause arglist: (arglist params: (arg varname: (identifier) @variable.parameter))))
(proc_defn returns: (returns_clause arglist: (arglist param: (arg varname: (identifier) @variable.parameter))))

(pred_defn name: (identifier) @function)
(pred_defn parameters: (arglist params: (arg varname: (identifier) @variable.parameter)))
(proc_defn parameters: (arglist param: (arg varname: (identifier) @variable.parameter)))

(lemma_defn name: (identifier) @function)
(lemma_defn parameters: (arglist params: (arg varname: (identifier) @variable.parameter)))
(lemma_defn parameters: (arglist param: (arg varname: (identifier) @variable.parameter)))

(axiom_defn name: (identifier) @function)
(axiom_defn parameters: (arglist params: (arg varname: (identifier) @variable.parameter)))
(axiom_defn parameters: (arglist param: (arg varname: (identifier) @variable.parameter)))

(case_defn (identifier) @funciton)
(case_defn parameters: (arglist params: (arg varname: (identifier) @variable.parameter)))
(case_defn parameters: (arglist param: (arg varname: (identifier) @variable.parameter)))
