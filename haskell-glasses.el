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

(defcustom glasses-infix-operators nil
  "Display glasses of all other infix operators"
  :group 'haskell-glasses
  :type '(alist :key-type symbol
                :value-type (group string string
                                   boolean (choice (const :tag "None" nil) face)))
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defun haskell-glasses-custom-set (symbol value)
  "Set value of the variable SYMBOL to VALUE and update overlay categories.
Used in :set parameter of some customized glasses variables."
  (set-default symbol value)
  (haskell-glasses-set-overlay-properties))


;;; Internal stuffs

;;; Utilities

(defmacro with-save (&rest body)
  `(save-excursion
     (save-match-data
       (block nil ,@body))))

(defmacro awhen (test &rest body)
  `(let ((it ,test))
     (when it
       ,@body)))

(defmacro awhens (tests &rest body)
  `(let ((them (list ,@tests)))
     (when (every #'identity them)
       ,@body)))

(defmacro let-when (bindings &rest body)
  `(let ,bindings
     (when (and ,@(mapcar #'car bindings))
       ,@body)))

(defmacro aif (test conclusion &optional alternative)
  `(let ((it ,test))
     (if it
         ,conclusion
       ,alternative)))

;;; Glasses overlay

(defvar haskell-glasses-predefined-list
  `((glasses-lambda-dot ,glasses-lambda-face) (glasses-infix-operators nil)))

(defun haskell-glasses-fix-overlay-cursor (overlay after beg end &optional length)
  (if after (haskell-glasses-mode 1)
    (haskell-glasses-mode -1)))

(defun haskell-glasses-set-overlay-properties ()
  "Set properties of glasses overlays.
Consider current setting of user variables."
  (flet ()
    (dolist (pg haskell-glasses-predefined-list)
      (put (car pg) 'face (cadr pg))
      (put (car pg) 'insert-in-front-hooks
           (list #'haskell-glasses-fix-overlay-cursor)))
    (dolist (io glasses-infix-operators)
      (put (car io) 'face (nth 4 io))
      (put (car io) 'insert-in-front-hooks
           (list #'haskell-glasses-fix-overlay-cursor)))))

(defun haskell-glasses-overlay-p (overlay)
  "Return whether OVERLAY is an overlay of haskell glasses mode."
  (let ((cat (overlay-get overlay 'category))) 
    (or (assoc cat haskell-glasses-predefined-list)
        (assoc cat glasses-infix-operators))))

(defun haskell-glasses-make-overlay (beg end category)
  "Create and return scholastic overlay over the region from BEG to END.
CATEGORY is the overlay category."
  (let ((overlay (make-overlay beg end)))
    (overlay-put overlay 'category category)
    overlay))

;;; Glasses regexp

(defconst | "\\|")
(defconst \( "\\(")
(defconst \(?: "\\(?:" )
(defconst \) "\\)")
(defconst cid (concat \(?: "\\<[[:upper:]][[:alnum:]_']*"  \) ))
(defconst vid (concat \(?: "\\<[[:lower:]_][[:alnum:]_']*" \) ))
(defconst mid (concat \(?: \(?: cid  "[.]" \) "*" \) ))
(defconst qid (concat mid \(?: vid | cid \) ))

(defconst id1 "\\<\\(?:[[:lower:]]+\\|[[:upper:]]+\\)'*\\([[:digit:]]+\\)'*\\>")
(defconst id2 "\\<\\(?:[[:alpha:]_]+\\)'*\\([[:digit:]]+\\)'*\\>")

(defun qot (del)
  (concat del \(?: "[^" del "\\]" | \(?: "[^\\]" | \(?: "\\\\\\\\" \) "*" \) "\\\\." \) "*" del
          | del \(?: "\\\\\\\\" \) "*" "\\\\." \(?: "[^" del "\\]" | \(?: "[^\\]" | \(?: "\\\\\\\\" \) "*" \) "\\\\." \) "*" del))
(defconst str (qot "\""))
(defconst chr (qot "'"))

(defconst lncmt
  (concat \( "--"
          \(?: "[-[:alnum:][:blank:](){}|;_`'\",]"
          | "\\["
          | "\\]"
          \)
          ".*" \)
          ))

(defun iop (opreg)
  (concat \(?:
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

(defun vid (varreg &optional trailing-blanks-p)
  (concat "\\(?1:\\<" (regexp-quote varreg) "\\>\\)"
          (if trailing-blanks-p "\\(?3:[[:blank:]]+\\)" "[^'_]")
          |
          "\\(?2:\\<" (regexp-quote varreg) "\\)$" ))

;;; Glasses skips

(defvar haskell-glasses-skip-list nil)
(defun haskell-glasses-skip-list (&optional lim)
  (labels ((escape-p (pos)
              (let ((sls 0))
                (while (and (<= sls pos)
                            (char-equal ?\\ (char-before (- pos sls))))
                  (setq sls (1+ sls)))
                (oddp sls)))
           (skip-quo (quo)
             (with-save
              (while (re-search-forward quo (point-max) t)
                (unless (escape-p (1- (point))) 
                  (return (point))))
              (return (point-max))))
           (skip-par (opn cls)
             (with-save
              (while (re-search-forward
                      (concat \( opn \) | \( cls \))
                      (point-max) t)
                (if (match-beginning 2)
                    (return (point))
                  (awhen (skip-par opn cls)
                         (goto-char it))))
              (return (point-max))))
           (skip-str () (skip-quo "\""))
           (skip-chr () (skip-quo "\'"))
           (skip-cmt () (skip-par "{-" "-}")))
    (with-save
     (goto-char (point-min))
     (let ((r (concat \( "\"" \)
                      | \( "{-" \)
                      | lncmt
                      | "[^[:alnum:]_']" \( "\'" \)
                      |  \( "^\'" \)
                      ))
           (skips nil)
           (lim (or lim (point-max))))
       (while (and (<= (point) lim) (re-search-forward r lim t))
         (awhen
          (or
           (awhens ((match-beginning 1) (skip-str)) them)
           (awhens ((match-beginning 2) (skip-cmt)) them)
           (awhens ((match-beginning 3) (match-end 3)) them)
           (awhens ((or (match-beginning 4) (match-beginning 5)) (skip-chr)) them))
          (goto-char (cadr it))
          (setq skips (pushnew it skips))))
       skips))))

(defun haskell-glasses-skip-glasses-p (beg end)
  (with-save
   (unless haskell-glasses-skip-list
     (setq haskell-glasses-skip-list (haskell-glasses-skip-list)))
   (dolist (area haskell-glasses-skip-list)
     (when (or (and (<= (car area) beg) (< beg (cadr area)))
               (and (< (car area) end) (<= end (cadr area))))
       (return area)))))

(defun haskell-glasses-find-lamb-dot (pos &optional lim)
  (let ((lim (or lim (point-max)))
        (args (concat \( "(" \) | \( "\\[" \) | \( "{" \)
                      | \(?: (iop "->") \) ;Hey! I'm here.
                      | "[#@~._'\"]" | ")" | "\\]" | "}"
                      | \( "[[:punct:]]" \)))
        (skips (remove-if (lambda (skip)
                            (or (< (cadr skip) pos) (< lim (car skip))))
                          haskell-glasses-skip-list)))
    (labels ((skip-par (o c)
                (with-save
                 (while (re-search-forward
                         (concat \( (regexp-quote o) \)
                                 | \( (regexp-quote c) \)) lim t)
                   (awhen (or (awhens ((match-beginning 1) (match-end 1)) them)
                              (awhens ((match-beginning 2) (match-end 2)) them))
                          (let ((dot it))
                            (aif (haskell-glasses-skip-glasses-p (car dot) (cadr dot))
                                 (goto-char (1- (cadr it)))
                                 (if (match-beginning 2)
                                     (return (cadr dot))
                                   (awhen (skip-par o c) (goto-char it)))))))
                 (return lim)))
             (skip-tpl () (skip-par "(" ")"))
             (skip-lst () (skip-par "[" "]"))
             (skip-rcd () (skip-par "{" "}")))
      (with-save
       (goto-char pos)
       (while (and (<= (point) lim) (re-search-forward args lim t))
         (awhen (or
                 (awhens ((match-beginning 1) (match-end 1)) them)
                 (awhens ((match-beginning 2) (match-end 2)) them)
                 (awhens ((match-beginning 3) (match-end 3)) them)
                 (awhens ((match-beginning 4) (match-end 4)) them)
                 (awhens ((match-beginning 5) (match-end 5)) them)
                 (awhens ((match-beginning 6) (match-end 6)) them))
                (aif (haskell-glasses-skip-glasses-p (car it) (cadr it))
                     (goto-char (1- (cadr it)))
                     (progn
                       (when (match-beginning 6) (return))
                       (awhen (or
                               (awhens ((match-beginning 1) (skip-tpl)) them)
                               (awhens ((match-beginning 2) (skip-lst)) them)
                               (awhens ((match-beginning 3) (skip-rcd)) them))
                              (goto-char (1- (cadr it))))
                       (awhen (or
                               (awhens ((match-beginning 4) (match-end 4)) them)
                               (awhens ((match-beginning 5) (match-end 5)) them))
                              (return it))))))))))

;;; Glasses makers

(defmacro haskell-glasses-make-glasses (mat tgl-p makers)
  `(lambda (beg end)
     (when ,tgl-p
       (let ((case-fold-search nil))
         (with-save
          (goto-char beg)
          (while (re-search-forward ,mat end t)
            ,@(mapcar
               (lambda (m)
                 (if (atom (car m))
                     `(let ((sb (match-beginning ,(car m)))
                            (se (match-end ,(car m))))
                        (when (and sb se (not (haskell-glasses-skip-glasses-p sb se))) 
                          (funcall ,(cadr m) sb se)))
                   `(progn
                      ,@(mapcar
                         (lambda (n)
                           `(let  ((sb (match-beginning ,n))
                                   (se (match-end ,n)))
                              (when (and sb se (not (haskell-glasses-skip-glasses-p sb se))) 
                                (funcall ,(cadr m) sb se))))
                         (car m)))))
               makers)))))))

(defmacro haskell-glasses-make-iop-glasses (mat gls tgl-p &rest body)
  `(haskell-glasses-make-glasses (iop ,mat) ,tgl-p
    (((1 2) (lambda (sb se)
              (with-save
               (goto-char se)
               ,@body
               (unless (some #'haskell-glasses-overlay-p (overlays-at sb))
                 (let ((os (haskell-glasses-make-overlay sb se ,gls)))
                   (overlay-put os 'display (eval ,gls))))))))))

(defmacro haskell-glasses-make-vid-glasses (mat gls tgl-p tbk &rest body)
  `(haskell-glasses-make-glasses (vid ,mat ,tbk) ,tgl-p
    (((1 2) (lambda (sb se)
              (with-save
               ,@body
               (let ((os (haskell-glasses-make-overlay sb se ,gls)))
                 (overlay-put os 'display (eval ,gls))))))
     ((3  ) (lambda (sb se)
              (with-save
               ,@body
               (let ((os (haskell-glasses-make-overlay sb se ,gls)))
                 (overlay-put os 'display ""))))))))

;;; Glasses displays

(defvar haskell-glasses-display-list nil)

(defun haskell-glasses-display-scholastic (beg end)
  "Make haskell code in the region from BEG to END scholastic."
  (map nil (lambda (f) (funcall f beg end)) haskell-glasses-display-list)
  (dolist (io glasses-infix-operators)
    (let ((sym (nth 0 io))
          (inf (nth 1 io))
          (gls (nth 2 io))
          (tgl (nth 3 io)))
      (when tgl
        (set sym gls)
        (funcall (haskell-glasses-make-iop-glasses inf sym tgl) beg end)))))

(defun haskell-glasses-display-normal (beg end)
  "Display code in the region from BEG to END to their normal state."
  (setq haskell-glasses-skip-list nil)
  (dolist (o (overlays-in beg end))
    (when (haskell-glasses-overlay-p o)
      (delete-overlay o))))

(defun haskell-glasses-display-normal-cpp (beg end)
  "Display cpp code in the region from BEG to END to their normal state."
  (with-save
   (goto-char beg)
   (while (<= (line-end-position) end)
     (goto-char (line-beginning-position))
     (when (and (current-word) (char-equal ?# (string-to-char (current-word))))
       (haskell-glasses-display-normal (line-beginning-position) (line-end-position)))
     (next-line))))

(defun haskell-glasses-display-change (beg end)
  "After-change function updating haskell glass overlays."
  (let ((beg-line (with-save (goto-char beg)
           (if (re-search-backward "^[^[:space:]\n]" (point-min) t)
               (point)
             (line-beginning-position))))
	(end-line (with-save (goto-char end) (line-end-position))))
    (haskell-glasses-display-normal beg-line end-line)
    (haskell-glasses-display-scholastic beg-line end-line)
    (haskell-glasses-display-normal-cpp beg-line end-line)))

;;; Glasses defines

(defmacro define-haskell-glasses (name mat tgl-p face makers)
  `(setq haskell-glasses-predefined-list
         (pushnew (list ',name ,face) haskell-glasses-predefined-list)
         haskell-glasses-display-list
         (pushnew (haskell-glasses-make-glasses ,mat ,tgl-p ,makers) haskell-glasses-display-list)))

(defmacro define-haskell-iop-glasses (name mat tgl-p face &rest body)
  `(setq haskell-glasses-predefined-list
         (pushnew (list ',name ,face) haskell-glasses-predefined-list)
         haskell-glasses-display-list
         (pushnew (haskell-glasses-make-iop-glasses ,mat ',name ,tgl-p ,@body) haskell-glasses-display-list)))

(defmacro define-haskell-vid-glasses (name mat tgl-p face tbk &rest body)
  `(setq haskell-glasses-predefined-list
         (pushnew (list ',name ,face) haskell-glasses-predefined-list)
         haskell-glasses-display-list
         (pushnew (haskell-glasses-make-vid-glasses ,mat ',name ,tgl-p ,tbk ,@body) haskell-glasses-display-list)))


;;; Predefined glasses

(define-haskell-iop-glasses glasses-arrow-right         "->"        glasses-arrow-p  glasses-arrow-face)
(define-haskell-iop-glasses glasses-arrow-left          "<-"        glasses-arrow-p  glasses-arrow-face)
(define-haskell-iop-glasses glasses-arrow-double-right  "=>"        glasses-arrow-p  glasses-arrow-face)
(define-haskell-iop-glasses glasses-equiv-equal         "=="        glasses-equiv-p  glasses-equiv-face)
(define-haskell-iop-glasses glasses-equiv-not-equal     "/="        glasses-equiv-p  glasses-equiv-face)
(define-haskell-iop-glasses glasses-equiv-greater-equal ">="        glasses-equiv-p  glasses-equiv-face)
(define-haskell-iop-glasses glasses-equiv-less-equal    "<="        glasses-equiv-p  glasses-equiv-face)
(define-haskell-iop-glasses glasses-equiv-equiv         "="         glasses-equiv-p  glasses-equiv-face)
(define-haskell-iop-glasses glasses-logic-and           "&&"        glasses-logic-p  glasses-logic-face)
(define-haskell-iop-glasses glasses-logic-or            "||"        glasses-logic-p  glasses-logic-face)
(define-haskell-vid-glasses glasses-logic-not           "not"       glasses-logic-p  glasses-logic-face    t)
(define-haskell-vid-glasses glasses-bottom-undefined    "undefined" glasses-bottom-p glasses-bottom-face nil)

(define-haskell-iop-glasses glasses-fun-compose "." glasses-fun-compose-p glasses-fun-compose-face
  (when (re-search-backward (concat \( cid \) ) (line-beginning-position) t)
    (let ((pse (match-end 1)))
      (when (and pse (= pse sb))
        (return)))))

(define-haskell-iop-glasses glasses-lambda-lambda "\\" glasses-lambda-p glasses-lambda-face
  (goto-char sb)
  (aif (haskell-glasses-find-lamb-dot se (point-max))
       (let  ((os (haskell-glasses-make-overlay (car it) (cadr it) 'glasses-lambda-dot)))
         (overlay-put os 'display glasses-lambda-dot))
       (return)))

(define-haskell-glasses glasses-subscript (if glasses-subscript-inhibit-mix-case-p id1 id2)
  glasses-subscript-p glasses-subscript-face
  ((1 (lambda (sb se)
        (let  ((os (haskell-glasses-make-overlay sb se 'glasses-subscript)))
          (overlay-put os 'display
                       `((height ,glasses-subscript-height)
                         (raise ,glasses-subscript-raise))))))))


;;; Minor mode definition

;;;###autoload
(define-minor-mode haskell-glasses-mode
  "Minor mode for making haskell code scholastic.
With a prefix argument ARG, enable the mode if ARG is positive,
and disable it otherwise.  If called from Lisp, enable the mode
if ARG is omitted or nil.  When this mode is active, it tries to
display hasekll code scholastic"
  :group 'haskell-glasses :lighter " oho"
  (with-save
   (widen)
   (haskell-glasses-display-normal (point-min) (point-max))
   (haskell-glasses-set-overlay-properties)
   (if haskell-glasses-mode
       (jit-lock-register 'haskell-glasses-display-change)
     (jit-lock-unregister 'haskell-glasses-display-change))))

;;; Announce

(provide 'haskell-glasses)

;;; haskell-glasses.el ends here