;; Based on the vpr syntax table
(require 'treesit)

;; First, clone the tree-sitter-raven repository
;; locally and build it using "make", resulting in libtree-sitter-raven.so.
;; Then, copy libtree-sitter-raven.so into ~/.emacs.d/tree-sitter/.
;; Finally, evaluate the contents of this buffer.

(defvar raven-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?/ ". 124b" table)
    (modify-syntax-entry ?* ". 23" table)
    (modify-syntax-entry ?\n "> b" table)
    table))

;; (treesit-query-validate 'raven
;;                         '((apply callee: (expr (value (location name_or_field: (identifier) @font-lock-function-call-face))))))

(defvar raven--treesit-settings
  (treesit-font-lock-rules
   :feature 'comment
   :language 'raven
   '([(comment) (block_comment)] @font-lock-comment-face)

   :feature 'string
   :language 'raven
   '((string) @font-lock-string-face)

   :feature 'keyword
   :language 'raven
   '([(kwd_spec)
      (kwd_inv)
      (kwd_au)
      (kwd_atomic)
      (kwd_axiom)
      (kwd_atomic_token)
      (kwd_auto)
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
      (kwd_requires)
      (kwd_return)
      (kwd_returns)
      (kwd_type)
      (kwd_var)
      (kwd_with)
      (kwd_while)
      (kwd_quantifier)] @font-lock-keyword-face)

   :feature 'definition
   :language 'raven
   '((module_def (module_header (mod_identifier) @font-lock-type-face))
     (field_def (identifier) @font-lock-variable-name-face)
     (var_def (bound_var_type (identifier) @font-lock-variable-name-face))
     (type_decl (mod_identifier) @font-lock-type-face)
     (case_defn (identifier) @font-lock-function-name-face)
     (case_defn (variant_args (bound_var (identifier) @font-lock-variable-name-face)))
     (callable_decl (identifier) @font-lock-variable-name-face)
     (callable_decl_out_vars (identifier) @font-lock-variable-name-face))

   :feature 'builtin
   :language 'raven
   '((kwd_own) @font-lock-builtin-face)

   :feature 'function
   :language 'raven
   '((call_expr (call) @font-lock-function-call-face))

   :feature 'constant
   :language 'raven
   '((kwd_const) @font-lock-constant-face)

   :feature 'type
   :language 'raven
   '((type_expr) @font-lock-type-face)

   :feature 'number
   :language 'raven
   '([(number)] @font-lock-constant-face)

   :feature 'operator
   :language 'raven
   '([(op_implies) (op_iff) (op_eq) (op_eqeq) (op_neq) (op_leq) (op_geq)
      (op_lt) (op_gt) (op_or) (op_and) (op_subseteq) (op_in) (op_not_in)
      (op_not) (op_plus) (op_minus) (op_div) (op_mul) (op_coloneq)
      (op_coloncolon) (op_dot) (op_qmark) (op_colonpipe)]
       @font-lock-operator-face)))

;; borrow from python's treesit mode
(defun raven--treesit-defun-name (node)
  "Return the defun name of NODE.
Return nil if there is no name or if NODE is not a defun node."
  (pcase (treesit-node-type node)
    ((or "proc_def" "func_def")
     (treesit-node-text
      (treesit-node-child-by-field-name
       node "identifier")
      t))))

(define-derived-mode raven-ts-mode prog-mode "Raven"
  "Major mode for editing Raven files, using tree-sitter library."
  :syntax-table raven-syntax-table
  (when (treesit-ready-p 'raven)
    (treesit-parser-create 'raven)
    (setq-local treesit-font-lock-feature-list
                '((comment definition function operator variable)
                  (keyword string type)
                  (builtin constant number)))
    (setq-local treesit-font-lock-settings raven--treesit-settings)
    (setq-local treesit-defun-type-regexp (rx (or "func" "proc" "lemma" "axiom" "pred")))
    (setq-local treesit-defun-name-function
                nil)
    (treesit-major-mode-setup)
    (add-to-list 'auto-mode-alist '("\\.rav\\'" . raven-ts-mode))))

(provide 'raven-ts-mode)
