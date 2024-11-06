;;; Comments, text, & string is never formented
[
  (block_comment)
  (comment_text)
  (comment)
  (string)
] @leaf

; Allow blank line before
[
  (defn)
] @allow_blank_line_before


; Surround spaces
[
  (binop_op) (unop_op)
  (qmark) (ternary_colon)
  (kwd_import)
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
  (kwd_data)
  (kwd_case)
  (kwd_auto)
  (kwd_lemma)
  (kwd_axiom)
  (kwd_func)
  (coloncolon)
  (trigger)
  (proc_body)
  (pred_body)
  (eq)
  (coloneq)
] @prepend_space @append_space

; Append spaces
[
  (seperator)
] @append_space

; Input softlines before and after all comments. This means that the input
; decides if a comment should have line breaks before or after. A line comment
; always ends with a line break.
[
  (block_comment)
  (comment)
] @prepend_input_softline

; Input softline after block comments unless followed by comma or semicolon, as
; they are always put directly after.
(
  (block_comment) @append_input_softline
  .
  [ (seperator) ]* @do_nothing
)

; Append line breaks. If there is a comment following, we don't add anything,
; because the input softlines and spaces above will already have sorted out the
; formatting.
(
  [
    (func_defn) (axiom_defn) (pred_defn) (lemma_defn) (proc_defn) (field_defn) (val_defn) (interface_defn) (import_stmt) (module_defn)
  ] @append_spaced_softline
  .
  [
    (block_comment)
    (comment)
  ]* @do_nothing
)

(block_comment) @multi_line_indent_all

; Allow line break after block comments
(
  (block_comment)
  .
  _ @prepend_input_softline
)

; Append softlines, unless followed by comments.
(
  [
   (seperator) (end_stmt)
  ] @append_spaced_softline
  .
  [(block_comment) (comment)]* @do_nothing
)

; Prepend softlines before dots
(_
  (dot) @prepend_empty_softline
)

; This patterns is duplicated for all nodes that can contain curly braces.
; Hoping to be able to generalise them like this:
; (_
;   .
;   "{" @prepend_space
;   (#for! block declaration_list enum_variant_list field_declaration_list)
; )
; Perhaps even the built in #match! can do this

(module_defn name: (identifier) @prepend_space)
(func_defn name: (identifier) @prepend_space)
(axiom_defn name: (identifier) @prepend_space)
(lemma_defn name: (identifier) @prepend_space)
(pred_defn name: (identifier) @prepend_space)
(proc_defn name: (identifier) @prepend_space)
(case_defn) @prepend_spaced_softline


(func_defn returns: (returns_clause) @prepend_space)
(proc_defn returns: (returns_clause) @prepend_space)

(axiom_defn io: (io_spec_clause) @prepend_space)
(lemma_defn io: (io_spec_clause) @prepend_space)
(proc_defn io: (io_spec_clause) @prepend_space)

(module_defn body: (interface_body) @prepend_space)
(interface_defn body: (interface_body) @prepend_space)
(data_defn body: (data_body) @prepend_space)
(data_defn body: (data_body case: (case_defn) @append_spaced_softline))
(func_defn body: (proc_body) @prepend_space)
(lemma_defn body: (proc_body) @prepend_space)
(proc_defn body: (proc_body) @prepend_space)
(pred_defn body: (pred_body) @prepend_space)

(data_defn (lcurly) @append_spaced_softline @append_indent_start)
(data_defn (rcurly) @prepend_spaced_softline @prepend_indent_end)

(proc_body
  .
  (lcurly) @append_spaced_softline @append_indent_start
  _
  (rcurly) @prepend_spaced_softline @prepend_indent_end
  .)
(pred_body
  .
  (lcurly) @append_spaced_softline @append_indent_start
  _
  (rcurly) @prepend_spaced_softline @prepend_indent_end
  .)
(interface_body
  .
  (lcurly) @append_spaced_softline @append_indent_start
  _
  (rcurly) @prepend_spaced_softline @prepend_indent_end
  .)
(map_literal
  .
  (map_literal_l) @append_spaced_softline @append_indent_start
  _
  (map_literal_r) @prepend_spaced_softline @prepend_indent_end
  .)


(arg vartype: (type) @prepend_space)

[ (seperator) (end_stmt)] @prepend_antispace
