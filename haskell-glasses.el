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
;; This file defines the `haskell-glasses-mode' minor mode, which displays haskell
;; code scholastic. Alternatively, you
;; can say you want the code in some given face (e.g. Italic, Subscript).

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

(defcustom glasses-type-p t
  "Display type annotation scholastic"
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-type-arrow "→"
  "Display a -> b as a → b"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-constraint-arrow "⇒"
  "Display C a => a as C a ⇒ a"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-type-face nil
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

(defcustom glasses-equiv-great-equal "≥"
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

(defcustom glasses-logic-op-p t
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

(defcustom glasses-logic-op-face nil
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
  (put 'glasses-lambda-lambda 'face glasses-lambda-face)
  (put 'glasses-lambda-dot 'face glasses-lambda-face)
  (put 'glasses-type-arrow 'face glasses-type-face)
  (put 'glasses-constraint-arrow 'face glasses-type-face)
  (put 'glasses-equiv-equiv 'face glasses-equiv-face)
  (put 'glasses-equiv-equal 'face glasses-equiv-face)
  (put 'glasses-equiv-not-equal 'face glasses-equiv-face)
  (put 'glasses-equiv-great-equal 'face glasses-equiv-face)
  (put 'glasses-equiv-less-equal 'face glasses-equiv-face)
  (put 'glasses-subscript 'face glasses-subscript-face)
  (put 'glasses-fun-compose 'face glasses-fun-compose-face)
  (put 'glasses-logic-or 'face glasses-logic-op-face)
  (put 'glasses-logic-and 'face glasses-logic-op-face)
  (put 'glasses-logic-not 'face glasses-logic-op-face)
  (put 'glasses-bottom-undefined 'face glasses-bottom-face)
  (put 'glasses-lambda-lambda 'insert-in-front-hooks '(fix-floating-insertion))
  (put 'glasses-lambda-dot 'insert-in-front-hooks '(fix-floating-insertion))
  (put 'glasses-type-arrow 'insert-in-front-hooks '(fix-floating-insertion))
  (put 'glasses-constraint-arrow 'insert-in-front-hooks '(fix-floating-insertion))
  (put 'glasses-equiv-equiv 'insert-in-front-hooks '(fix-floating-insertion))
  (put 'glasses-equiv-equal 'insert-in-front-hooks '(fix-floating-insertion))
  (put 'glasses-equiv-not-equal 'insert-in-front-hooks '(fix-floating-insertion))
  (put 'glasses-equiv-great-equal 'insert-in-front-hooks '(fix-floating-insertion))
  (put 'glasses-equiv-less-equal 'insert-in-front-hooks '(fix-floating-insertion))
  (put 'glasses-subscript 'insert-in-front-hooks '(fix-floating-insertion))
  (put 'glasses-fun-compose 'insert-in-front-hooks '(fix-floating-insertion))
  (put 'glasses-logic-or 'insert-in-front-hooks '(fix-floating-insertion))
  (put 'glasses-logic-and 'insert-in-front-hooks '(fix-floating-insertion))
  (put 'glasses-logic-not 'insert-in-front-hooks '(fix-floating-insertion))
  (put 'glasses-bottom-undefined 'insert-in-front-hooks '(fix-floating-insertion)))

(haskell-glasses-set-overlay-properties)

(defun haskell-glasses-overlay-p (overlay)
  "Return whether OVERLAY is an overlay of haskell glasses mode."
  (memq (overlay-get overlay 'category)
	'(glasses-lambda-lambda
          glasses-lambda-dot
          glasses-type-arrow
          glasses-constraint-arrow
          glasses-equiv-equiv
          glasses-equiv-equal
          glasses-equiv-not-equal
          glasses-equiv-less-equal
          glasses-equiv-great-equal
          glasses-subscript
          glasses-fun-compose
          glasses-logic-or
          glasses-logic-and
          glasses-logic-not
          glasses-bottom-undefined)))

(defun haskell-glasses-make-overlay (beg end category)
  "Create and return scholastic overlay over the region from BEG to END.
CATEGORY is the overlay category."
  (let ((overlay (make-overlay beg end)))
    (overlay-put overlay 'category category)
    overlay))

(defconst | "\\|")
(defconst cid "[[:upper:]][[:alnum:]_']*")
(defconst vid "\\<[[:lower:]_][[:alnum:]_']*\\>")
(defconst qid (concat "\\(" cid "[.]\\)*" vid))
(defconst par "\\(([^()]*?)\\|(.*)\\)")
(defconst blk "[[:blank:]]*")
(defconst lexeme  (concat blk "\\(" qid | par    "\\)" blk))
(defconst llexeme (concat blk "\\(" qid | par | "(\\)" blk))
(defconst rlexeme (concat blk "\\(" qid | par | ")\\)" blk))
(defun iop (opreg) (concat "\\([^[:punct:]]\\|[()_'\"]\\)\\(" opreg "\\)\\([^[:punct:]]\\|[()_'\"]\\)"))
(defconst hstr "\"\\([^\"\\]\\|\\([^\\]\\|\\(\\\\\\\\\\)*\\)\\\\.\\)*\"\\|\"\\(\\\\\\\\\\)*\\\\.\\([^\"\\]\\|\\([^\\]\\|\\(\\\\\\\\\\)*\\)\\\\.\\)*\"")

(defun haskell-search-id-subscript (beg end maker)
  (let ((case-fold-search nil))
    (save-excursion
      (save-match-data
	(goto-char beg)
	(while (re-search-forward
                (if glasses-subscript-inhibit-mix-case-p
                    "\\<\\([[:lower:]]+\\|[[:upper:]]+\\)'*\\([[:digit:]]+\\)\\>"
                  "\\<\\([[:alpha:]_]+\\)'*\\([[:digit:]]+\\)\\>")
                end t)
          (let  ((sb (match-beginning 2))
                 (se (match-end 2)))
            (when (and sb se)
              (funcall maker sb se))))))))

(defun haskell-search-fun-compose (beg end maker)
  (let ((case-fold-search nil))
    (save-excursion
      (save-match-data
	(goto-char beg)
	(while (re-search-forward
                (concat llexeme "\\([.]\\)" rlexeme)
                end t)
          (let  ((lpb (match-beginning 3))
                 (lpe (match-end 3))
                 (rpb (match-beginning 7))
                 (rpe (match-end 7))
                 (sb (match-beginning 4))
                 (se (match-end 4)))
            (when (and sb se)
              (goto-char sb)
              (funcall maker sb se))
            (when (and lpb lpe)
              (haskell-search-fun-compose lpb lpe maker))
            (when (and rpb rpe)
              (haskell-search-fun-compose rpb rpe maker))))))))

(defun haskell-search-line-lambda (beg end maker)
  (let ((case-fold-search nil))
    (save-excursion
      (save-match-data
	(goto-char beg)
	(while (re-search-forward
                (concat "\\(\\\\\\)\\(" lexeme "\\)+\\(->\\)")
                end t)
          (let  ((lb (match-beginning 1))
                 (le (match-end 1))
                 (db (match-beginning 6))
                 (de (match-end 6)))
            (when (and lb db)
              (funcall maker lb le db de))))))))

(defun haskell-search-type-annot (beg end maker1 maker2)
  (let ((case-fold-search nil))
    (save-excursion
      (save-match-data
	(goto-char beg)
	(while (re-search-forward (iop "->") end t)
          (let  ((ab (match-beginning 2))
                 (ae (match-end 2)))
            (when (and ab)
              (goto-char ae)
              (funcall maker1 ab ae))))
        (goto-char beg)
        (while (re-search-forward (iop "=>") end t)
          (let  ((ab (match-beginning 2))
                 (ae (match-end 2)))
            (when (and ab)
              (goto-char ae)
              (funcall maker2 ab ae))))))))

(defun haskell-search-equiv (beg end maker1 maker2 maker3 maker4 maker5)
  (let ((case-fold-search nil))
    (save-excursion
      (save-match-data
	(goto-char beg)
	(while (re-search-forward (iop "==") end t)
          (let  ((ab (match-beginning 2))
                 (ae (match-end 2)))
            (when (and ab)
              (goto-char ae)
              (funcall maker1 ab ae))))
        (goto-char beg)
        (while (re-search-forward (iop "/=") end t)
          (let  ((ab (match-beginning 2))
                 (ae (match-end 2)))
            (when (and ab)
              (goto-char ae)
              (funcall maker2 ab ae))))
        (goto-char beg)
        (while (re-search-forward (iop "=") end t)
          (let  ((ab (match-beginning 2))
                 (ae (match-end 2)))
            (when (and ab)
              (goto-char ae)
              (funcall maker3 ab ae))))
        (goto-char beg)
        (while (re-search-forward (iop ">=") end t)
          (let  ((ab (match-beginning 2))
                 (ae (match-end 2)))
            (when (and ab)
              (goto-char ae)
              (funcall maker4 ab ae))))
        (goto-char beg)
        (while (re-search-forward (iop "<=") end t)
          (let  ((ab (match-beginning 2))
                 (ae (match-end 2)))
            (when (and ab)
              (goto-char ae)
              (funcall maker5 ab ae))))))))

(defun haskell-search-logic-op (beg end maker1 maker2 maker3)
  (let ((case-fold-search nil))
    (save-excursion
      (save-match-data
	(goto-char beg)
	(while (re-search-forward (iop "&&") end t)
          (let  ((ab (match-beginning 2))
                 (ae (match-end 2)))
            (when (and ab)
              (goto-char ae)
              (funcall maker1 ab ae))))
        (goto-char beg)
        (while (re-search-forward (iop "||") end t)
          (let  ((ab (match-beginning 2))
                 (ae (match-end 2)))
            (when (and ab)
              (goto-char ae)
              (funcall maker2 ab ae))))
        (goto-char beg)
        (while (re-search-forward "\\(\\<not\\>[[:blank:]]*\\)" end t)
          (let  ((ab (match-beginning 1))
                 (ae (match-end 1)))
            (when (and ab)
              (funcall maker3 ab ae))))))))

(defun haskell-search-bottom (beg end maker)
  (let ((case-fold-search nil))
    (save-excursion
      (save-match-data
	(goto-char beg)
	(while (re-search-forward "\\(\\<undefined\\>\\)[^']\\|\\(\\<undefined$\\)" end t)
          (let  ((sb1 (match-beginning 1))
                 (se1 (match-end 1))
                 (sb2 (match-beginning 2))
                 (se2 (match-end 2)))
            (when (and sb1 se1)
              (funcall maker sb1 se1))
            (when (and sb2 se2)
              (funcall maker sb2 se2))))))))

(defun haskell-glasses-display-scholastic (beg end)
  "Make haskell code in the region from BEG to END scholastic."
  (haskell-search-fun-compose beg end
                              (lambda (cb ce)
                                (when glasses-fun-compose-p
                                  (let  ((os (haskell-glasses-make-overlay cb ce 'glasses-fun-compose)))
                                    (overlay-put os 'display glasses-fun-compose)))))
  (haskell-search-id-subscript beg end
                                (lambda (sb se)
                                  (when glasses-subscript-p
                                    (let  ((os (haskell-glasses-make-overlay sb se 'glasses-subscript)))
                                      (overlay-put os 'display `((height ,glasses-subscript-height)
                                                                 (raise ,glasses-subscript-raise)))))))
  (haskell-search-line-lambda beg end
                              (lambda (lb le db de)
                                (when glasses-lambda-p
                                  (let  ((ol (haskell-glasses-make-overlay lb le 'glasses-lambda-lambda))
                                         (od (haskell-glasses-make-overlay db de 'glasses-lambda-dot)))
                                    (overlay-put ol 'display glasses-lambda-lambda)
                                    (overlay-put od 'display glasses-lambda-dot)))))
  (haskell-search-type-annot beg end
                             (lambda (ab ae)
                               (when glasses-type-p
                                 (unless (some 'haskell-glasses-overlay-p (overlays-at ab))
                                   (let ((oa (haskell-glasses-make-overlay ab ae 'glasses-type-arrow)))
                                     (overlay-put oa 'display glasses-type-arrow)))))
                             (lambda (ab ae)
                               (when glasses-type-p
                                 (unless (some 'haskell-glasses-overlay-p (overlays-at ab))
                                   (let ((oa (haskell-glasses-make-overlay ab ae 'glasses-constraint-arrow)))
                                     (overlay-put oa 'display glasses-constraint-arrow))))))
  (haskell-search-equiv beg end
                        (lambda (ab ae)
                          (when glasses-equiv-p
                            (unless (some 'haskell-glasses-overlay-p (overlays-at ab))
                              (let ((oa (haskell-glasses-make-overlay ab ae 'glasses-equiv-equal)))
                                (overlay-put oa 'display glasses-equiv-equal)))))
                        (lambda (ab ae)
                          (when glasses-equiv-p
                            (unless (some 'haskell-glasses-overlay-p (overlays-at ab))
                              (let ((oa (haskell-glasses-make-overlay ab ae 'glasses-equiv-not-equal)))
                                (overlay-put oa 'display glasses-equiv-not-equal)))))
                        (lambda (ab ae)
                          (when glasses-equiv-p
                            (unless (some 'haskell-glasses-overlay-p (overlays-at ab))
                              (let ((oa (haskell-glasses-make-overlay ab ae 'glasses-equiv-equiv)))
                                (overlay-put oa 'display glasses-equiv-equiv)))))
                        (lambda (ab ae)
                          (when glasses-equiv-p
                            (unless (some 'haskell-glasses-overlay-p (overlays-at ab))
                              (let ((oa (haskell-glasses-make-overlay ab ae 'glasses-equiv-great-equal)))
                                (overlay-put oa 'display glasses-equiv-great-equal)))))
                        (lambda (ab ae)
                          (when glasses-equiv-p
                            (unless (some 'haskell-glasses-overlay-p (overlays-at ab))
                              (let ((oa (haskell-glasses-make-overlay ab ae 'glasses-equiv-less-equal)))
                                (overlay-put oa 'display glasses-equiv-less-equal))))))
  (haskell-search-logic-op beg end
                           (lambda (ab ae)
                             (when glasses-logic-op-p
                               (unless (some 'haskell-glasses-overlay-p (overlays-at ab))
                                 (let ((oa (haskell-glasses-make-overlay ab ae 'glasses-logic-and)))
                                   (overlay-put oa 'display glasses-logic-and)))))
                           (lambda (ab ae)
                             (when glasses-logic-op-p
                               (unless (some 'haskell-glasses-overlay-p (overlays-at ab))
                                 (let ((oa (haskell-glasses-make-overlay ab ae 'glasses-logic-or)))
                                   (overlay-put oa 'display glasses-logic-or)))))
                           (lambda (ab ae)
                             (when glasses-logic-op-p
                               (unless (some 'haskell-glasses-overlay-p (overlays-at ab))
                                 (let ((oa (haskell-glasses-make-overlay ab ae 'glasses-logic-not)))
                                   (overlay-put oa 'display glasses-logic-not))))))
  (haskell-search-bottom beg end
                         (lambda (cb ce)
                           (when glasses-bottom-p
                             (let  ((os (haskell-glasses-make-overlay cb ce 'glasses-bottom-undefined)))
                               (overlay-put os 'display glasses-bottom-undefined))))))

(defun haskell-glasses-display-normal (beg end)
  "Display code in the region from BEG to END to their normal state."
  (dolist (o (overlays-in beg end))
    (when (haskell-glasses-overlay-p o)
      (delete-overlay o))))

(defun haskell-glasses-display-normal-cpp (beg end)
  "Display cpp code in the region from BEG to END to their normal state."
  (save-excursion
    (goto-char beg)
    (while (<= (line-end-position) end)
      (goto-char (line-beginning-position))
      (when (and (current-word) (char-equal ?# (string-to-char (current-word))))
        (dolist (o (overlays-in (line-beginning-position) (line-end-position)))
          (when (haskell-glasses-overlay-p o)
            (delete-overlay o))))
      (next-line))))

(defun haskell-glasses-display-normal-comment (beg end)
  "Display comment code in the region from BEG to END to their normal state."
  (save-excursion
    (goto-char beg)
    (while (<= (line-end-position) end)
      (goto-char (line-beginning-position))
      (when (re-search-forward "\\(--\\)" (line-end-position) t)
        (let ((cb (match-beginning 1)))
          (when cb
            (dolist (o (overlays-in cb (line-end-position)))
              (when (haskell-glasses-overlay-p o)
                (delete-overlay o))))))
      (next-line))))

(defun haskell-glasses-display-normal-string (beg end)
  "Display string in the region from BEG to END to their normal state."
  (save-excursion
    (goto-char beg)
    (while (re-search-forward
            (concat "\\([^\\]" hstr | "^" hstr "\\)") end t)
      (let ((cb (match-beginning 1))
            (ce (match-end 1)))
          (when (and cb ce)
            (dolist (o (overlays-in cb ce))
              (when (haskell-glasses-overlay-p o)
                (delete-overlay o))))))))

(defun haskell-glasses-change (beg end)
  "After-change function updating haskell glass overlays."
  (let ((beg-line (save-excursion (goto-char beg) (line-beginning-position)))
	(end-line (save-excursion (goto-char end) (line-end-position))))
    (haskell-glasses-display-normal beg-line end-line)
    (haskell-glasses-display-scholastic beg-line end-line)
    (haskell-glasses-display-normal-cpp beg-line end-line)
    (haskell-glasses-display-normal-comment beg-line end-line)
    (haskell-glasses-display-normal-string beg-line end-line)))

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
