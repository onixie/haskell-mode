;;; haskell-glasses.el --- make haskell code scholastic

;; Copyright (C) 1999-2013 Free Software Foundation, Inc.
;; Copyright (C) 2013 Shen

;; Author: Shen <onixie@gmail.com>
;; Maintainer: Shen <onixie@gmail.com>

;; This file is not part of GNU Emacs.

;; This file is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This file defines a minor mode for making haskell code scholastic. 
;;
;; This file defines the `haskell-glasses-mode' minor mode, which displays
;; haskell code scholastic.

;;; History
;;
;; The start of this mode is inspired by `glasses-mode' by Milan Zamazal.

;;; Code:

;;; User variables

(defgroup haskell-glasses nil
  "Make haskell code scholastic"
  :version "0.1"
  :group 'haskell
  :prefix 'haskell-glasses)

(defcustom glasses-lambda-p t
  "Display lambda abstraction scholastic"
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-lambda-lambda "λ"
  "Display (\\x -> x) as (λx -> x)"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-lambda-dot "."
  "Display (\\x -> x) as (\\x . x)"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-lambda-face nil
  "Face to be put on lambda abstractions.
If it is nil, no face is placed at the lambda abstractions. "
  :group 'haskell-glasses
  :type '(choice (const :tag "None" nil) face)
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-arrow-p t
  "Display type annotation scholastic"
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-arrow-right "→"
  "Display a -> b as a → b"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-arrow-left "←"
  "Display a <- b as a ← b"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-arrow-double-right "⇒"
  "Display C a => a as C a ⇒ a"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-arrow-face nil
  "Face to be put on type annotations.
If it is nil, no face is placed at the lambda abstractions. "
  :group 'haskell-glasses
  :type '(choice (const :tag "None" nil) face)
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-equiv-p t
  "Display equivalance declaration scholastic"
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-equiv-equiv "≡"
  "Display declaration a = b as a ≡ b"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-equiv-equal "="
  "Display equal test a == b as a = b"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-equiv-not-equal "≠"
  "Display equal test a /= b as a ≠ b"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-equiv-greater-equal "≥"
  "Display equal test a >= b as a ≥ b"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-equiv-less-equal "≤"
  "Display equal test a <= b as a ≤ b"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-equiv-face nil
  "Face to be put on equivalance declaration.
If it is nil, no face is placed at the lambda abstractions. "
  :group 'haskell-glasses
  :type '(choice (const :tag "None" nil) face)
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-subscript-p t
  "Display t1 as t₁ , A1 as A₁."
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-subscript-inhibit-mix-case-p t
  "Display Tt1 as Tt1 but TT1 as TT₁."
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-subscript-face nil
  "Face to be put on subscript.
If it is nil, no face is placed at the lambda abstractions. "
  :group 'haskell-glasses
  :type '(choice (const :tag "None" nil) face)
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-subscript-height 0.75
  "Height of the subscript number. "
  :group 'haskell-glasses
  :type 'number
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-subscript-raise 0
  "Raise of the subscript number. "
  :group 'haskell-glasses
  :type 'number
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-fun-compose-p t
  "Display function composition scholastic"
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-fun-compose "∘"
  "Display f . g as f ∘ g"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-fun-compose-face nil
  "Face to be put on function composition
If it is nil, no face is placed at the function composition. "
  :group 'haskell-glasses
  :type '(choice (const :tag "None" nil) face)
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-logic-p t
  "Display logic op scholastic"
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-logic-and "∧"
  "Display A && B as A ∧ B"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-logic-or "∨"
  "Display A || B as A ∨ B"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-logic-not "¬"
  "Display not A as ¬A"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-logic-face nil
  "Face to be put on lambda abstractions.
If it is nil, no face is placed at the lambda abstractions. "
  :group 'haskell-glasses
  :type '(choice (const :tag "None" nil) face)
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-bottom-p t
  "Display undefined scholastic"
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-bottom-undefined "⊥"
  "Display undefined as ⊥"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-bottom-face nil
  "Face to be put on bottom.
If it is nil, no face is placed at bottom."
  :group 'haskell-glasses
  :type '(choice (const :tag "None" nil) face)
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defvar predefined-glasses
  `((glasses-lambda-lambda     ,glasses-lambda-face)
    (glasses-lambda-dot         ,glasses-lambda-face)
    (glasses-arrow-right        ,glasses-arrow-face)
    (glasses-arrow-left         ,glasses-arrow-face)
    (glasses-arrow-double-right ,glasses-arrow-face)
    (glasses-equiv-equiv         ,glasses-equiv-face)
    (glasses-equiv-equal         ,glasses-equiv-face)
    (glasses-equiv-not-equal     ,glasses-equiv-face)
    (glasses-equiv-greater-equal ,glasses-equiv-face)
    (glasses-equiv-less-equal    ,glasses-equiv-face)
    (glasses-subscript           ,glasses-subscript-face)
    (glasses-fun-compose         ,glasses-fun-compose-face)
    (glasses-logic-or            ,glasses-logic-face)
    (glasses-logic-and           ,glasses-logic-face)
    (glasses-logic-not           ,glasses-logic-face)
    (glasses-bottom-undefined    ,glasses-bottom-face)))

(defun haskell-glasses-custom-set (symbol value)
  "Set value of the variable SYMBOL to VALUE and update overlay categories.
Used in :set parameter of some customized glasses variables."
  (set-default symbol value)
  (haskell-glasses-set-overlay-properties))

;;; Utility functions

(defun fix-floating-insertion (overlay after beg end &optional length)
  (if after (haskell-glasses-mode 1) (haskell-glasses-mode -1)))

(defun haskell-glasses-set-overlay-properties ()
  "Set properties of glasses overlays.
Consider current setting of user variables."
  (dolist (pg predefined-glasses)
    (put (car pg) 'face (cadr pg))
    (put (car pg) 'insert-in-front-hooks (list #'fix-floating-insertion))))

(haskell-glasses-set-overlay-properties)

(defun haskell-glasses-overlay-p (overlay)
  "Return whether OVERLAY is an overlay of haskell glasses mode."
  (assoc (overlay-get overlay 'category) predefined-glasses))

(defun haskell-glasses-make-overlay (beg end category)
  "Create and return scholastic overlay over the region from BEG to END.
CATEGORY is the overlay category."
  (let ((overlay (make-overlay beg end)))
    (overlay-put overlay 'category category)
    overlay))

;;; 
(defconst | "\\|")
(defconst \( "\\(")
(defconst \(?: "\\(?:" )
(defconst \) "\\)")
(defconst cid (concat \(?: "\\<[[:upper:]][[:alnum:]_']*"  \) ))
(defconst vid (concat \(?: "\\<[[:lower:]_][[:alnum:]_']*" \) ))
(defconst mid (concat \(?: \(?: cid  "[.]" \) "*" \) ))
(defconst qid (concat mid \(?: vid | cid \) ))

(defun qot (del)
  (concat
   del
      \(?: "[^" del "\\]" | \(?: "[^\\]" | \(?: "\\\\\\\\" \) "*" \) "\\\\." \) "*"
   del
   |
   del
      \(?: "\\\\\\\\" \) "*" "\\\\." \(?: "[^" del "\\]" | \(?: "[^\\]" | \(?: "\\\\\\\\" \) "*" \) "\\\\." \) "*"
   del))

(defconst str (qot "\""))
(defconst chr (qot "'"))

;;; 
(defconst id1 "\\<\\(?:[[:lower:]]+\\|[[:upper:]]+\\)'*\\([[:digit:]]+\\)'*\\>")
(defconst id2 "\\<\\(?:[[:alpha:]_]+\\)'*\\([[:digit:]]+\\)'*\\>")

(defun iop (opreg)
  (concat
   \(?:
   \(?: "[^[:punct:]]" | "[]}()_'\"]" \)
   mid \( (regexp-quote opreg) \)
   \(?: "[^[:punct:]]" | "[[{()_'\"]" \)
   \)
   | 
   \(?:
   "^"
   mid \( (regexp-quote opreg) \)
   \(?: "[^[:punct:]]" | "[[{()_'\"]" \)
   \)
   ))

(defconst vid-not "\\(\\<not\\>[[:blank:]]*\\)")
(defconst vid-undefined "\\(\\<undefined\\>\\)[^']\\|\\(\\<undefined$\\)")
(defconst lncmt (concat \( "--" \(?: "[-[:alnum:][:blank:](){}|;_`'\",]" | "\\[" | "\\]" \) ".*" \) ))

(defun haskell-glasses-skip-glasses (beg end)
  (save-excursion
    (save-match-data
      (goto-char (point-min))
      (block nil (let ((r (concat \( "\"" \) | "[^[:alnum:]_']" \( "\'" \) | \( "{-" \) | lncmt )))
                   (while (re-search-forward r end t)
                     (let ((s (match-beginning 1))
                           (c (match-beginning 2))
                           (bc (match-beginning 3))
                           (lcb (match-beginning 4))
                           (lce (match-end 4)))
                       (when (and lcb (or (and (< lcb beg) (<= beg lce))
                                          (and (< lcb end) (<= end lce))))
                         (return t))
                       (let ((f (or s c bc)))
                         (when f (goto-char f)
                               (forward-sexp) ;Yep, sexp is black magic here.
                               (when (or (and (< f beg) (<= beg (point)))
                                         (and (< f end) (<= end (point))))
                                 (return t)))))))))))

(defmacro haskell-glasses-make-glasses (mat makers)
  `(lambda (beg end)
     (let ((case-fold-search nil))
       (save-excursion
         (save-match-data
           (goto-char beg)
           (while (re-search-forward ,mat end t)
             ,@(mapcar
                (lambda (m)
                  (if (atom (car m))
                      `(let  ((sb (match-beginning ,(car m)))
                              (se (match-end ,(car m))))
                         (when (and sb se (not (haskell-glasses-skip-glasses sb se))) 
                           (funcall ,(cadr m) sb se)))
                    `(progn
                       ,@(mapcar (lambda (n)
                                   `(let  ((sb (match-beginning ,n))
                                           (se (match-end ,n)))
                                      (when (and sb se (not (haskell-glasses-skip-glasses sb se))) 
                                        (funcall ,(cadr m) sb se))))
                                 (car m)))))
                makers)))))))

(defmacro haskell-glasses-make-iop-glasses (mat gls &rest body)
  `(haskell-glasses-make-glasses (iop ,mat)
    (((1 2) (lambda (sb se)
          (block nil
            (goto-char se)
            ,@body
            (unless (some #'haskell-glasses-overlay-p (overlays-at sb))
              (let ((os (haskell-glasses-make-overlay sb se ',gls)))
                (overlay-put os 'display ,gls)))))))))

(defun haskell-glasses-make-subscript-glasses (beg end)
  (funcall
   (haskell-glasses-make-glasses (if glasses-subscript-inhibit-mix-case-p id1 id2)
    ((1 (lambda (sb se)
          (let  ((os (haskell-glasses-make-overlay sb se 'glasses-subscript)))
            (overlay-put os 'display `((height ,glasses-subscript-height)
                                       (raise ,glasses-subscript-raise)))))))) beg end))

(defun haskell-glasses-find-lamb-dot (pos lim)
  (save-excursion
    (save-match-data
      (goto-char pos)
      (block nil
        (let ((r (concat \( "\"" \)
                         | "[^[:alnum:]_']" \( "\'" \)
                         | \( "{" \)
                         | \( "(" \)
                         | \( "\\[" \)
                         | \( "->" \)
                         | "[@~.]"
                         | \( "[[:punct:]]" \))))
          (while (re-search-forward r lim t)
            (let ((s (match-beginning 1))
                  (c (match-beginning 2))
                  (b (match-beginning 3))
                  (p (match-beginning 4))
                  (sp (match-beginning 5))
                  (ob (match-beginning 6))
                  (oe (match-end 6))
                  (n (match-beginning 7)))
              (when n
                (return))
              (when (and ob oe)
                (return (cons ob oe)))
              (let ((f (or s c b p sp)))
                (when f (goto-char f)
                      (forward-sexp))))))))))

(defun haskell-glasses-find-lamb-lamb (pos lim)
  (save-excursion
    (save-match-data
      (goto-char pos)
      (block nil
        (let ((r (concat \( "\"" \)
                         | "[^[:alnum:]_']" \( "\'" \)
                         | \( "}" \)
                         | \( ")" \)
                         | \( "\\]" \)
                         | \( (iop "\\") \))))
          (while (re-search-backward r lim t)
            (let ((s (match-end 1))
                  (c (match-end 2))
                  (b (match-end 3))
                  (p (match-end 4))
                  (sp (match-end 5))
                  (ob (match-beginning 6))
                  (oe (match-end 6)))
              (when (and ob oe)
                (let ((d (haskell-glasses-find-lamb-dot oe (+ pos 2))))
                  (if (and d (= pos (cdr d)))
                      (return (cons ob oe))
                    (return))))
              (let ((f (or s c b p sp)))
                (when f (goto-char f)
                      (backward-sexp))))))))))

(defun haskell-glasses-make-lambda-glasses (beg end)
  (funcall
   (haskell-glasses-make-iop-glasses
    "\\" glasses-lambda-lambda
    (save-excursion
      (save-match-data
        (goto-char sb)
        (let ((d (haskell-glasses-find-lamb-dot se (point-max))))
          (unless d (return)))))) beg end)
  (funcall
   (haskell-glasses-make-iop-glasses
    "->" glasses-lambda-dot
    (save-excursion
      (save-match-data
        (goto-char se)
        (let ((d (haskell-glasses-find-lamb-lamb se (point-min))))
          (unless d (return)))))) beg end))

(defun haskell-glasses-make-fun-compose-glasses (beg end)
  (funcall 
   (haskell-glasses-make-iop-glasses
    "." glasses-fun-compose
    (save-excursion
      (save-match-data
        (when (re-search-backward (concat \( cid \) ) (line-beginning-position) t)
          (let ((pse (match-end 1)))
            (when (and pse (= pse sb))
              (return))))))) beg end))

(defun haskell-glasses-make-arrow-glasses (beg end)
  (funcall (haskell-glasses-make-iop-glasses "->" glasses-arrow-right) beg end)
  (funcall (haskell-glasses-make-iop-glasses "<-" glasses-arrow-left) beg end)
  (funcall (haskell-glasses-make-iop-glasses "=>" glasses-arrow-double-right) beg end))

(defun haskell-glasses-make-equiv-glasses (beg end)
  (funcall (haskell-glasses-make-iop-glasses "==" glasses-equiv-equal) beg end)
  (funcall (haskell-glasses-make-iop-glasses "/=" glasses-equiv-not-equal) beg end)
  (funcall (haskell-glasses-make-iop-glasses ">=" glasses-equiv-greater-equal) beg end)
  (funcall (haskell-glasses-make-iop-glasses "<=" glasses-equiv-less-equal) beg end)
  (funcall (haskell-glasses-make-iop-glasses "="  glasses-equiv-equiv) beg end))

(defun haskell-glasses-make-logic-glasses (beg end)
  (funcall (haskell-glasses-make-iop-glasses "&&" glasses-logic-and) beg end)
  (funcall (haskell-glasses-make-iop-glasses "||" glasses-logic-or) beg end)
  (funcall (haskell-glasses-make-glasses vid-not
            ((1 (lambda (sb se)
                  (let  ((os (haskell-glasses-make-overlay sb se 'glasses-logic-not)))
                    (overlay-put os 'display glasses-logic-not)))))) beg end))

(defun haskell-glasses-make-bottom-glasses (beg end)
  (funcall (haskell-glasses-make-glasses vid-undefined
            (((1 2) (lambda (sb se)
                (let  ((os (haskell-glasses-make-overlay sb se 'glasses-bottom-undefined)))
                  (overlay-put os 'display glasses-bottom-undefined)))))) beg end))

(defun haskell-glasses-display-scholastic (beg end)
  "Make haskell code in the region from BEG to END scholastic."
  (haskell-glasses-make-subscript-glasses   beg end)
  (haskell-glasses-make-fun-compose-glasses beg end)
  (haskell-glasses-make-lambda-glasses beg end)
  (haskell-glasses-make-arrow-glasses beg end)
  (haskell-glasses-make-equiv-glasses beg end)
  (haskell-glasses-make-logic-glasses beg end)
  (haskell-glasses-make-bottom-glasses beg end))

(defun haskell-glasses-display-normal (beg end)
  "Display code in the region from BEG to END to their normal state."
  (dolist (o (overlays-in beg end))
    (when (haskell-glasses-overlay-p o)
      (delete-overlay o))))

(defun haskell-glasses-remove-glasses (beg end)
  (dolist (o (overlays-in (+ beg 1) end))
    (when (haskell-glasses-overlay-p o)
      (delete-overlay o))))

(defun haskell-glasses-display-normal-cpp (beg end)
  "Display cpp code in the region from BEG to END to their normal state."
  (save-excursion
    (goto-char beg)
      (while (<= (line-end-position) end)
        (goto-char (line-beginning-position))
        (when (and (current-word) (char-equal ?# (string-to-char (current-word))))
          (haskell-glasses-remove-glasses (line-beginning-position) (line-end-position)))
        (next-line))))

(defun haskell-glasses-change (beg end)
  "After-change function updating haskell glass overlays."
  (let ((beg-line (save-excursion
                    (save-match-data
                      (goto-char beg)
                      (if (re-search-backward "^[^[:space:]\n]" (point-min) t)
                          (point)
                        (line-beginning-position)))))
	(end-line (save-excursion (goto-char end) (line-end-position))))
    (haskell-glasses-display-normal beg-line end-line)
    (haskell-glasses-display-scholastic beg-line end-line)
    (haskell-glasses-display-normal-cpp beg-line end-line)))

;;; Minor mode definition

;;;###autoload
(define-minor-mode haskell-glasses-mode
  "Minor mode for making haskell code scholastic.
With a prefix argument ARG, enable the mode if ARG is positive,
and disable it otherwise.  If called from Lisp, enable the mode
if ARG is omitted or nil.  When this mode is active, it tries to
display hasekll code scholastic"
  :group 'haskell-glasses :lighter " oho"
  (save-excursion
    (save-restriction
      (widen)
      ;; We erase all the overlays anyway, to avoid dual sight in some
      ;; circumstances
      (haskell-glasses-display-normal (point-min) (point-max))
      (if haskell-glasses-mode
	  (jit-lock-register 'haskell-glasses-change)
	(jit-lock-unregister 'haskell-glasses-change)))))

;;; Announce

(provide 'haskell-glasses)

;;; haskell-glasses.el ends here