(eval-and-compile
  (require 'proof-site)			; compilation for whyitp
  (proof-ready-for-assistant 'whyitp))

(require 'proof)

(defun set-vars ()
  "configure Proof General scripting for Why3ITP"
  (setq
   proof-terminal-string       	"\n" ;; TODO se mettre d'accord sur un proof terminal
   proof-script-comment-start	"(*"
   proof-script-comment-end	"*)"
   proof-showproof-command	"g\n"
   proof-undo-n-times-cmd       "pg_repeat undo %s;"
   proof-auto-multiple-files	 nil ;; no multiple files
 ))

(defun set-shell-vars()
  "configure Proof General shell for Why3ITP"
  (setq
   proof-shell-start-goals-regexp      "====================== Task ====================="
   proof-shell-restart-cmd             "r\n"
   proof-shell-end-goals-regexp        "================================================="
   proof-shell-quit-cmd		       "q\n"
   proof-shell-annotated-prompt-regexp "^> "
   proof-shell-error-regexp            "\\*\\*\\*\\|^.*Error:\\|^uncaught exception \\|^Exception- "
   proof-shell-init-cmd		       "fun pg_repeat f 0 = () | pg_repeat f n = (f(); pg_repeat f (n-1));"))

(defun set-prog-name ()
  (setq proof-prog-name (concat "why3shell " (replace-regexp-in-string ".whyitp" ".why" (buffer-file-name ())))))

(define-derived-mode whyitp-mode proof-mode
  "Why3ITP script" nil
  (set-vars)
  (set-prog-name)
  (proof-config-done))

(define-derived-mode whyitp-shell-mode proof-shell-mode
  "Why3ITP shell" nil
  (set-shell-vars)
  (proof-shell-config-done))

(define-derived-mode whyitp-response-mode proof-response-mode
  "Why3ITP response" nil
  (proof-response-config-done))

(define-derived-mode whyitp-goals-mode proof-goals-mode
  "Why3ITP goals" nil
  (proof-goals-config-done))

;; redo "undo" and "go to" proof general command for why3itp

(defun proof-undo-last-successful-command ()
  (interactive)
  (let (lastspan)
    ;; (save-excursion
    ;; (unless (proof-locked-region-empty-p)
    (if (setq lastspan (span-at-before (proof-unprocessed-begin) 'type))
        (progn
          (goto-char (span-start lastspan))
          (proof-goto-point))
      (error "Nothing to undo!"))))

(defun proof-goto-point ()
  "Undo last successful command at end of locked region."
  (interactive)
  (when proof-shell-busy
    (proof-interrupt-process)
    (proof-shell-wait))
  (if (not (proof-shell-live-buffer))
      (proof-shell-start) ;; start if not running
    ;; otherwise clear context
    (proof-script-remove-all-spans-and-deactivate)
    (proof-shell-clear-state)
    (with-current-buffer proof-shell-buffer
      (delete-region (point-min) (point-max)))
    (proof-minibuffer-cmd "r\n")
    (when proof-shell-busy
      (proof-shell-wait))
    (proof-assert-until-point)))

(provide 'whyitp)
