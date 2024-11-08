;;; Comments, text, identifier & string is never formented
[
  (block_comment)
  (comment_text)
  (comment)
  (string)
  (identifier)
] @leaf

; Allow blank line before
[
  (defn)
] @allow_blank_line_before


; Surround spaces
[
  (binop_op)
  (qmark) (ternary_colon)
  (kwd_bind)
  (kwd_atomic)
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
  (kwd_inhale)
  (kwd_exhale)
  (coloncolon)
  (trigger)
  (eq)
  (coloneq)
] @prepend_space @append_space
(kwd_own) @prepend_space

; Append spaces
[
  (seperator)
] @append_input_spaced_softline


(comment) @append_hardline @allow_blank_line_before

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

; Put breaks between defns
(
 (defn)
 .
 (defn) @prepend_hardline
)

; Put breaks between statements
(
 (stmt)
 .
 (stmt) @prepend_spaced_softline
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

; This patterns is duplicated for all nodes that can contain curly braces.
; Hoping to be able to generalise them like this:
; (_
;   .
;   "{" @prepend_space
;   (#for! block declaration_list enum_variant_list field_declaration_list)
; )
; Perhaps even the built in #match! can do this

(module_defn name: (identifier) @prepend_space)
(interface_defn typecons: ((colon) (type) @prepend_space))
(module_defn typecons: ((colon) (type) @prepend_space))

(func_defn name: (identifier) @prepend_space @append_indent_start (proc_body))

(axiom_defn name: (identifier) @prepend_space @append_indent_start _ @append_indent_end .)
(lemma_defn name: (identifier) @prepend_space @append_indent_start body: (proc_body))
(proc_defn name: (identifier) @prepend_space @append_indent_start (proc_body))
(rep_defn name: (identifier) @append_indent_start (data_defn))
(rep_defn name: (identifier) @append_indent_start (type) @append_indent_end)
(case_defn) @prepend_spaced_softline



(func_defn returns: (returns_clause) @prepend_space)
(proc_defn returns: (returns_clause) @prepend_space)
(func_defn returns: (returns_clause) @prepend_spaced_softline)
(proc_defn returns: (returns_clause) @prepend_spaced_softline)

(func_defn io: (io_spec_clause) @prepend_spaced_softline)
(axiom_defn io: (io_spec_clause) @prepend_spaced_softline)
(lemma_defn io: (io_spec_clause) @prepend_spaced_softline)
(proc_defn io: (io_spec_clause) @prepend_spaced_softline)


(interface_defn (interface_body) @prepend_space !parameters)
(module_defn (interface_body) @prepend_space !parameters)
(interface_defn parameters: (type_cons) @append_indent_start body: (interface_body) @prepend_indent_end @prepend_space)
(module_defn parameters: (type_cons) @append_indent_start body: (interface_body) @prepend_indent_end @prepend_space)
(module_defn parameters: (type_cons) @append_indent_start type: ((_) (type) @prepend_indent_end @prepend_space))
(data_defn body: (data_body) @prepend_indent_end @prepend_space)
(data_defn body: (data_body case: (case_defn) @append_spaced_softline) )
(func_defn body: (proc_body) @prepend_space @prepend_indent_end)
(lemma_defn body: (proc_body) @prepend_space @prepend_indent_end)
(proc_defn body: (proc_body) @prepend_space @prepend_indent_end)

(data_defn (lcurly) @append_spaced_softline @append_indent_start)
(data_defn (rcurly) @prepend_spaced_softline @prepend_indent_end)

[(data_defn !body)
(data_defn !body)
(func_defn !body)
(lemma_defn !body)
(proc_defn !body)
(pred_defn !body)] @append_spaced_softline

(pred_defn name: (identifier) @append_indent_start (pred_body) @prepend_indent_end)
(pred_body
  .
  (lcurly) @prepend_input_softline @append_spaced_softline @append_indent_start
  _
  (rcurly) @prepend_input_softline @prepend_spaced_softline @prepend_indent_end
  .)

(proc_body
  .
  (lcurly) @prepend_input_softline @append_spaced_softline @append_indent_start
  _
  (rcurly) @prepend_input_softline @prepend_spaced_softline @prepend_indent_end
  .)

(interface_body
  .
  (lcurly) @append_spaced_softline @append_indent_start
  _
  (rcurly) @prepend_spaced_softline @prepend_indent_end
  .)
(map_literal_l) @append_input_softline @append_indent_start
(map_literal_r) @prepend_input_softline @prepend_indent_end

(ghost_code
  .
  (lghost) @append_spaced_softline @append_indent_start
  _
  (rghost) @prepend_spaced_softline @prepend_indent_end
  .)

(arg vartype: (type) @prepend_space)
(type_con supertype: _ @prepend_space)

; Make the invariant clauses spaced
(while_stmt . (kwd_while) @append_indent_start)
(while_stmt (invariant_spec_clause) @prepend_spaced_softline)
; Make the last invariant clause unindented
(while_stmt (proc_body) @prepend_indent_end .)

(type_cons) @prepend_antispace
[ (seperator) (end_stmt) ] @prepend_antispace
