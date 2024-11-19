;; Based on the vpr syntax table
(require 'treesit)
(require 'subr)

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

(defun raven-auto-check-update ()
  (interactive)
  (let ((currdir buffer-file-name) (result 1))
    (with-temp-buffer
      (setq result (call-process "raven" nil t nil currdir)))
    (setq mode-name (if (= result 0) '(" Raven: ✓") '(" Raven: !")))))

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
    (setq-local treesit-defun-name-function nil)
    (treesit-major-mode-setup))
  (raven-auto-check-update))
(add-to-list 'auto-mode-alist '("\\.rav\\'" . raven-ts-mode))

(defcustom raven-ts-mode-location-re-one-line
  "File \"\\([^\"]*?\\)\", line \\([0-9]*\\), columns \\([0-9]*\\)-\\([0-9]*\\):\n"
  "Regular expression for locations that span one line.")
(defvar raven-ts-mode-location-re-one-line-properties
  [(identity :filename)
   (string-to-number :start-line :end-line)
   (string-to-number :start-column)
   (string-to-number :end-column)])
(defcustom raven-ts-mode-location-re-multiline
  "File \"\\([^\"]*?\\)\", line \\([0-9]*\\), column \\([0-9]*\\) to line \\([0-9]*\\), column \\([0-9]*\\):\n."
  "Regular expression for locations that span multiple lines.")
(defvar raven-ts-mode-location-re-multiline-properties
  '[(identity :filename)
    (string-to-number :start-line)
    (string-to-number :start-column)
    (string-to-number :end-line)
    (string-to-number :end-column)])
(defun raven-ts-mode-re-associate (properties)
  "Associate properties PROPERTIES with the current regex match."
  (let (output)
    (dotimes (i (length properties))
      (let ((coercion (car (aref properties i))))
        (dolist (key (cdr (aref properties i)))
          (let* ((fontified (match-string (+ i 1)))
                 (string (substring-no-properties fontified))
                 (typed (apply coercion `(,string))))
            (setq output (plist-put output key typed))))))
    output))

(defun raven-ts-mode-nearest-match (re1 re2 thunk1 thunk2)
  "Match the first regex of RE1 and RE2 by backtracking.
Call FORM1 if re1 matches first, and FORM2 if re2 matches first."
  (interactive "vRe1: \nvRe2: \naThunk1: \naThunk2")
  (when (symbolp re1) (setq re1 (eval re1)))
  (when (symbolp re2) (setq re2 (eval re2)))
  (let ((pmax (+ 1 (point-max)))
        (point-re1)
        (point-re2))
    (setq point-re1 (save-mark-and-excursion (if (re-search-forward re1 nil t nil) (point) pmax)))
    (setq point-re2 (save-mark-and-excursion (if (re-search-forward re2 nil t nil) (point) pmax)))
    (cond ((<= pmax (min point-re1 point-re2)) nil)
          ((<= point-re1 point-re2) (prog1 (re-search-forward re1 nil t nil) (apply thunk1 '())))
          (t (prog1 (re-search-forward re2 nil t nil) (apply thunk2 '()))))))

(defcustom raven-ts-mode-error-name-alist
  '(("Error" . Generic)
    ("Lexical Error" . Lexical)
    ("Syntax Error" . Syntax)
    ("Type Error" . Type)
    ("Internal Error" . Internal)
    ("Unsupported Error" . Unsupported)
    ("Verification Error" . Verification)
    ("Related Location" . RelatedLoc))
  "An alist mapping strings to error constructors in RAVEN-TS-MODE-ERROR-KIND")

(defcustom raven-ts-mode-error-level-alist
  '((Generic . error)
    (Lexical . error)
    (Syntax . error)
    (Type . error)
    (Internal . error)
    (Unsupported . error)
    (Verification . error)
    (RelatedLoc . info))
  "An alist mapping strings to error constructors in RAVEN-TS-MODE-ERROR-KIND")

(defun raven-ts-mode-string-to-error-kind (string)
  "Convert STRING to its kind of error"
  (alist-get string raven-ts-mode-error-name-alist nil nil 'string-equal))

(defvar raven-ts-mode-error-kind
  '(Generic Lexical Syntax Type Internal Unsupported Verification RelatedLoc))

(defvar raven-ts-mode-error-re
  (let (res)
    (dolist (error-pair raven-ts-mode-error-name-alist)
      (push (car error-pair) res))
    (format "\\(%s\\): \\([^\r\n]*?\\)\r?\n" (s-join "\\|" res)))
  "Regex for errors emitted by raven.")

(defvar raven-ts-mode-error-re-properties
  [(raven-ts-mode-string-to-error-kind :error-kind) (identity :message)])

(defun raven-ts-mode-parse-next-error ()
  (interactive)
  (when (re-search-forward "\\[Error\\] " nil t nil)
      (let (error-properties)
        (raven-ts-mode-nearest-match raven-ts-mode-location-re-one-line
                                     raven-ts-mode-location-re-multiline
                                     (lambda () (setq error-properties (raven-ts-mode-re-associate raven-ts-mode-location-re-one-line-properties)))
                                     (lambda () (setq error-properties (raven-ts-mode-re-associate raven-ts-mode-location-re-multiline-properties))))
        (goto-char (match-end 0))
        ;; discard the context
        (re-search-forward raven-ts-mode-error-re nil t nil)
        (setq error-properties (nconc (raven-ts-mode-re-associate raven-ts-mode-error-re-properties) error-properties))
        error-properties)))

(defun raven-ts-mode-parse-flycheck-error (&optional output checker buffer)
  "Parse the string OUTPUT emitted by raven when run on BUFFER, with the
flycheck checker CHECKER. Return a list of errors."
  (interactive)
  (when (null output) (setq output (buffer-substring (point-min) (point-max))))
  (let ((errors '()))
    (with-temp-buffer
      (insert output)
      (goto-char 0)
      (while-let ((next-error (raven-ts-mode-parse-next-error)))
        (let ((level (alist-get (plist-get next-error :error-kind) raven-ts-mode-error-level-alist))
              (message (plist-get next-error :message))
              (line (plist-get next-error :start-line))
              (column (plist-get next-error :start-column))
              (end-column (plist-get next-error :end-column))
              (end-line (plist-get next-error :end-line))
              (filename (plist-get next-error :filename)))
          (push (flycheck-error-new :message message :line line :column column :end-column end-column :end-line end-line :filename filename :buffer buffer :checker checker :level level) errors))))
    (when (called-interactively-p) (message "returning errors: %S" errors))
    errors))

(flycheck-define-checker raven
  "A raven syntax checker using `raven`"
  :command ("raven" source-original)
  :error-parser raven-ts-mode-parse-flycheck-error
  :modes raven-ts-mode)

(defun raven-ts-mode-indent ()
  (interactive)
  (if (eq major-mode 'raven-ts-mode)
      (progn (call-process "ravenfmt" nil nil nil buffer-file-name)
             (revert-buffer nil t t))))

(defun raven-ts-mode-start-checker ()
  (interactive)
  (flycheck-mode)
  (flycheck-select-checker 'raven))

(add-hook 'raven-ts-mode-hook 'raven-ts-mode-start-checker)
(add-hook 'after-save-hook 'raven-ts-mode-indent)
(add-hook 'after-save-hook 'raven-auto-check-update)
(provide 'raven-ts-mode)
