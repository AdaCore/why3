
;; why3.el - GNU Emacs mode for Why3

(defvar why3-mode-hook nil)

(defvar why3-mode-map nil
  "Keymap for Why3 major mode")

(if why3-mode-map nil
  (setq why3-mode-map (make-keymap))
  ;; (define-key why3-mode-map "\C-c\C-c" 'why3-generate-obligations) **)
  ;; (define-key why3-mode-map "\C-c\C-a" 'why3-find-alternate-file) **)
  ;; (define-key why3-mode-map "\C-c\C-v" 'why3-viewer) **)
  (define-key why3-mode-map [(control return)] 'font-lock-fontify-buffer))

(setq auto-mode-alist
      (append
       '(("\\.\\(why\\|mlw\\)" . why3-mode))
       auto-mode-alist))

;; font-lock

(defun why3-regexp-opt (l)
  (concat "\\<" (concat (regexp-opt l t) "\\>")))

(defconst why3-font-lock-keywords-1
  (list
   ;; Note: comment font-lock is guaranteed by suitable syntax entries
   '("(\\*\\([^*)]\\([^*]\\|\\*[^)]\\)*\\)?\\*)" . font-lock-comment-face)
;   '("{}\\|{[^|]\\([^}]*\\)}" . font-lock-type-face)
   `(,(why3-regexp-opt '("invariant" "variant" "diverges" "requires" "ensures" "returns" "raises" "reads" "writes" "assert" "assume" "check")) . font-lock-type-face)
   `(,(why3-regexp-opt '("use" "clone" "namespace" "import" "export" "coinductive" "inductive" "external" "constant" "function" "predicate" "val" "exception" "axiom" "lemma" "goal" "type" "mutable" "model" "abstract" "private" "any" "match" "let" "rec" "in" "if" "then" "else" "begin" "end" "while" "for" "to" "downto" "do" "done" "loop" "absurd" "ghost" "try" "with" "theory" "uses" "module" "converter")) . font-lock-keyword-face)
   )
  "Minimal highlighting for Why3 mode")

(defvar why3-font-lock-keywords why3-font-lock-keywords-1
  "Default highlighting for Why3 mode")

(defvar why3-indent 2
  "How many spaces to indent in why3 mode.")
(make-variable-buffer-local 'why3-indent)

;; syntax

(defvar why3-mode-syntax-table nil
  "Syntax table for why3-mode")

(defun why3-create-syntax-table ()
  (if why3-mode-syntax-table
      ()
    (setq why3-mode-syntax-table (make-syntax-table))
    (set-syntax-table why3-mode-syntax-table)
    (modify-syntax-entry ?' "w" why3-mode-syntax-table)
    (modify-syntax-entry ?_ "w" why3-mode-syntax-table)
    ; comments
    (modify-syntax-entry ?\( ". 1" why3-mode-syntax-table)
    (modify-syntax-entry ?\) ". 4" why3-mode-syntax-table)
    (modify-syntax-entry ?* ". 23" why3-mode-syntax-table)
    ))

;indentation

;http://www.emacswiki.org/emacs/ModeTutorial
(defun why3-indent-line ()
  "Indent current line as why3 logic"
  (interactive)
  (save-excursion
    (beginning-of-line)
    ;(debug)
    (if (bobp)  ; Check for rule 1
        (indent-line-to 0)
      (let ((not-indented t) cur-indent)
        (if (looking-at "^[ \t]*end") ; Check for rule 2
            (progn
              (save-excursion
                (forward-line -1)
                (setq cur-indent (- (current-indentation) why3-indent)))
              (if (< cur-indent 0)
                  (setq cur-indent 0)))
          (progn
            (if (looking-at "^[ \t]*\\(logic\\|type\\|prop\\)") ; check for clone
                (progn
                  (save-excursion
                    (forward-line -1)
                    (if (looking-at "^[ \t]*\\(logic\\|type\\|prop\\).*,[ \t]*$")
                        (progn
                          (setq cur-indent (current-indentation))
                          (setq not-indented nil))
                      (if (looking-at "^[ \t]*clone.*with ")
                          (progn
                            (setq cur-indent (+ (current-indentation) why3-indent))
                            (setq not-indented nil)
                            ))))))
        ;For the definition its very badly done...
          (if (looking-at "^[ \t]*$")
	      ;; (save-excursion
	      ;; 	(forward-line -1)
	      ;; 	(setq cur-indent (current-indentation))
	      ;; 	(setq not-indented nil))
              (progn
                (setq cur-indent 0)
                (setq not-indented nil))
	    (if (not
		 (looking-at "^[ \t]*(\*.*"))
            (if (not
                 (looking-at "^[ \t]*\\(logic\\|type\\|axiom\\|goal\\|lemma\\|inductive\\|use\\|theory\\|clone\\)"))
                (save-excursion
                  (condition-case nil
                      (save-excursion
                        (backward-up-list)
                        (setq cur-indent (+ (current-column) 1))
                        (setq not-indented nil))
                    (error
                     (forward-line -1)
                     (if (looking-at
                          "^[ \t]*\\(logic\\|type\\|axiom\\|goal\\|lemma\\|inductive\\)")
                         (setq cur-indent (+ (current-indentation) why3-indent))
                       (setq cur-indent (current-indentation)))
                     (setq not-indented nil)))))))
          ;For inside theory or namespace
          (save-excursion
            (while not-indented
              (forward-line -1)
              (if (looking-at "^[ \t]*end") ; Check for rule 3
                  (progn
                    (setq cur-indent (current-indentation))
                    (setq not-indented nil))
                                        ; Check for rule 4
                (if (looking-at "^[ \t]*\\(theory\\|namespace\\)")
                    (progn
                      (setq cur-indent (+ (current-indentation) why3-indent))
                      (setq not-indented nil))
                  (if (bobp) ; Check for rule 5
                      (setq not-indented nil)))))))
        (if cur-indent
            (indent-line-to cur-indent)
          (indent-line-to 0)))))))

; compile will propose "why3ide file" is no Makefile is present

(add-hook 'why3-mode-hook
          (lambda ()
            (unless (file-exists-p "Makefile")
              (set (make-local-variable 'compile-command)
                   (let ((file (file-name-nondirectory buffer-file-name)))
                     (format "why3ide %s" file))))))



;; setting the mode
(defun why3-mode ()
  "Major mode for editing Why3 programs.

\\{why3-mode-map}"
  (interactive)
  (kill-all-local-variables)
  (why3-create-syntax-table)
  ; hilight
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults '(why3-font-lock-keywords))
  ; indentation
  ;(make-local-variable 'indent-line-function)
  ;(setq indent-line-function 'why3-indent-line)
  ; OCaml style comments for comment-region, comment-dwim, etc.
  (set (make-local-variable 'comment-start) "(*")
  (set (make-local-variable 'comment-end)   "*)")
  ; menu
  ; providing the mode
  (setq major-mode 'why3-mode)
  (setq mode-name "Why3")
  (use-local-map why3-mode-map)
  (font-lock-mode 1)
  ; (why3-menu)
  (run-hooks 'why3-mode-hook))

(provide 'why3)

