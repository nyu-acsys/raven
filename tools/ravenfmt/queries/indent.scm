;;; Comments, text, identifier & string is never formented
[
  (block_comment)
  (comment_text)
  (comment)
  (string)
  (identifier)
  (mod_identifier)
  (literal)
] @leaf


; Allow a blank line before any include statement
; that comes after an include statement
(
 (include_stmt)
 .
 (include_stmt) @allow_blank_line_before
)

[
  (member_def)
] @allow_blank_line_before


; Surround spaces
[
  (kwd_spec)
  (kwd_inv)
  (kwd_au)
  (kwd_atomic)
  (kwd_axiom)
  (kwd_atomic_token)
  (kwd_auto)
  (kwd_bool)
  (kwd_cas)
  (kwd_case)
  (kwd_data)
  (kwd_else)
  (kwd_ensures)
  (kwd_const)
  (kwd_field)
  (kwd_func)
  (kwd_ghost)
  (kwd_havoc)
  (kwd_if)
  (kwd_include)
  (kwd_module)
  (kwd_invariant)
  (kwd_import)
  (kwd_implicit)
  (kwd_lemma)
  (kwd_rep)
  (kwd_new)
  (kwd_perm)
  (kwd_proc)
  (kwd_real)
  (kwd_requires)
  (kwd_return)
  (kwd_returns)
  (kwd_type)
  (kwd_var)
  (kwd_with)
  (kwd_while)

  (op_eq)
  (op_in)
  (op_not_in)
  (op_not)
  (op_coloneq)
  (op_coloncolon)
  (op_dot)
  (op_qmark)
  (op_colonpipe)
] @prepend_space @append_space
(kwd_own) @prepend_space
(op_colon) @append_space
(kwd_quantifier) @append_space


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
  [ (op_comma) (op_semicolon) ]* @do_nothing
)

(comment) @append_hardline @allow_blank_line_before

; Append line breaks. If there is a comment following, we don't add anything,
; because the input softlines and spaces above will already have sorted out the
; formatting.
(
 (member_def) . (op_semicolon) @append_spaced_softline
  .
  [
    (block_comment)
    (comment)
  ]* @do_nothing
)

(
 (member_def)
  .
  [
    (block_comment)
    (comment)
  ]* @do_nothing
  .
  (member_def) @prepend_spaced_softline
)

(block_comment) @multi_line_indent_all

; Allow line break after block comments
(
  (block_comment)
  .
  _ @prepend_input_softline
)

; Surround the module header with indentations
(module_def (kwd_module) @append_indent_start (module_inst) @prepend_space @prepend_indent_end)
(module_def (kwd_module) @append_indent_start (module_impl) @prepend_indent_end)
; Surround the parameter list & return type with indentations
(module_def (module_header (mod_identifier) @append_indent_start) @append_indent_end)
(module_param_list (delim_lbracket) @append_begin_scope @append_indent_start (delim_rbracket) @prepend_end_scope @prepend_indent_end
                   (#scope_id! "module_params"))
(module_param_list (op_comma) @append_spaced_scoped_softline (#scope_id! "module_params"))
(module_inst_args (delim_lbracket) @append_begin_scope @append_indent_start (delim_rbracket) @prepend_end_scope @prepend_indent_end
                  (#scope_id! "module_inst_params"))
(module_inst_args (op_comma) @append_spaced_scoped_softline (#scope_id! "module_inst_params"))
(proc_def (proc_kind) @append_indent_start (proc_decl) @append_indent_end)
(func_def (func_decl (_) @append_indent_start) (delim_lbrace) @append_indent_end)
(func_def (func_decl (_) @append_indent_start) @append_indent_end .)
(data_expr (delim_lbrace) @append_begin_scope @append_indent_start @append_empty_scoped_softline
           (delim_rbrace) @prepend_end_scope @prepend_indent_end @prepend_empty_scoped_softline
           (#scope_id! "data_expr_body"))
(data_expr (case_defn) (op_semicolon)? @append_spaced_scoped_softline (#scope_id! "data_expr_body"))
(variant_args (delim_lparen) @append_begin_scope @append_indent_start
              (delim_rparen) @prepend_end_scope @prepend_indent_end
              (#scope_id! "variant_args"))
(variant_args (op_comma) @append_spaced_scoped_softline (#scope_id! "variant_args"))
(callable_decl (delim_lparen) @append_begin_scope @append_indent_start
               (delim_rparen) @prepend_end_scope @prepend_indent_end
               (#scope_id! "callable_decl_args"))
(callable_decl (var_decls_with_modifiers (op_comma) @append_spaced_scoped_softline
                                         (#scope_id! "callable_decl_args")))
(contract) @prepend_input_softline
(returns_clause (delim_lparen) @append_begin_scope @append_indent_start
                (delim_rparen) @prepend_end_scope @prepend_indent_end
                (#scope_id! "returns_clause")) @prepend_input_softline
(returns_clause (var_decls_with_modifiers (op_comma) @append_spaced_scoped_softline) (#scope_id! "variant_args"))
(tuple (delim_lparen) @append_begin_scope @append_indent_start @append_antispace
       (delim_rparen) @prepend_end_scope @prepend_indent_end
       (#scope_id! "tuple"))

([(op_iff) (op_and) (op_or) (op_implies)
  (op_neq) (op_eqeq)
  (op_lt) (op_gt) (op_leq) (op_geq) (op_subseteq)
  (op_mul) (op_div)] @append_spaced_scoped_softline @prepend_spaced_scoped_softline
  (#scope_id! "expr"))
(binop_add [(op_plus) (op_minus)] @append_spaced_scoped_softline @prepend_spaced_scoped_softline
           (#scope_id! "binop_add"))

(tuple (op_comma) @append_spaced_scoped_softline (#scope_id! "tuple"))
(own_expr (delim_lparen) @append_begin_scope @append_indent_start @append_antispace
          (delim_rparen) @prepend_end_scope @prepend_indent_end
          (#scope_id! "own_scope"))
(own_expr (op_comma) @append_spaced_scoped_softline (#scope_id! "own_scope"))
(call (delim_lparen) @append_begin_scope @append_indent_start @append_antispace
      (delim_rparen) @prepend_end_scope @prepend_indent_end
      (#scope_id! "call_scope"))
(call (op_comma) @append_spaced_scoped_softline (#scope_id! "call_scope"))
(type_expr_map (delim_lbracket) (op_comma) @append_space (delim_rbracket))
(type_expr_app (delim_lbracket) @append_begin_scope @append_indent_start
               (delim_rbracket) @prepend_end_scope @prepend_indent_end
               (#scope_id! "ty_app"))
(type_expr_app (op_comma) @append_spaced_scoped_softline (#scope_id! "ty_app"))
(module_param_list (delim_lbracket) @append_begin_scope @append_indent_start
                   (delim_rbracket) @prepend_end_scope @prepend_indent_end
                   (#scope_id! "module_params"))
(module_param_list (op_comma) @append_spaced_scoped_softline (#scope_id! "module_params"))

(
 ([(stmt)
  (stmt_desc)
  (stmt_wo_trailing_substmt)
  (stmt_no_short_if)
  (stmt_no_short_if_desc)
  (if_then_else_stmt_no_short_if)
  (while_stmt_no_short_if)] (op_semicolon) @append_spaced_softline
 .
 [(stmt)
  (stmt_desc)
  (stmt_wo_trailing_substmt)
  (stmt_no_short_if)
  (stmt_no_short_if_desc)
  (if_then_else_stmt_no_short_if)
  (while_stmt_no_short_if)])
 )
(
 ([(stmt)
  (stmt_desc)
  (stmt_wo_trailing_substmt)
  (stmt_no_short_if)
  (stmt_no_short_if_desc)
  (if_then_else_stmt_no_short_if)
  (while_stmt_no_short_if)]
 .
 [(stmt)
  (stmt_desc)
  (stmt_wo_trailing_substmt)
  (stmt_no_short_if)
  (stmt_no_short_if_desc)
  (if_then_else_stmt_no_short_if)
  (while_stmt_no_short_if)] @prepend_spaced_softline)
 )
(module_inst (delim_lbrace) @append_indent_start @append_spaced_softline
             (delim_rbrace) @prepend_indent_end @prepend_spaced_softline)
(block (delim_lbrace) @append_indent_start @append_spaced_softline
       (delim_rbrace) @prepend_indent_end @prepend_spaced_softline)
((expr)
        @prepend_begin_scope @append_end_scope (#scope_id! "expr") )
(func_def (delim_lbrace) @prepend_space @prepend_indent_start @append_spaced_softline
          (delim_rbrace) @prepend_indent_end @prepend_spaced_softline)
(proc_def (block (delim_lbrace) @prepend_space))
(ghost_block (delim_lghostbrace) @append_indent_start @append_spaced_softline
             (delim_rghostbrace) @prepend_indent_end @prepend_spaced_softline)
(if_then_stmt (stmt (stmt_desc (stmt_wo_trailing_substmt (block (delim_lbrace) @prepend_space)))))
(if_then_else_stmt (stmt (stmt_desc (stmt_wo_trailing_substmt (block (delim_lbrace) @prepend_space)))))
(while_stmt (block (delim_lbrace) @prepend_space))
(while_stmt (stmt (stmt_desc (stmt_wo_trailing_substmt (block (delim_lbrace) @prepend_space)))))

; Make the invariant clauses spaced
( (kwd_while) @append_indent_start )
(loop_contract (expr) @prepend_indent_start @append_indent_end)
( (kwd_while) (loop_contract) @prepend_spaced_softline)
; Make the last invariant clause unindented
( (kwd_while) [(block) (stmt_no_short_if)] @prepend_space @prepend_indent_end .)
[ (op_semicolon) (op_comma) ] @prepend_antispace

