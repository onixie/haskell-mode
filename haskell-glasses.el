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

(require 'cl)

;;; User variables

(defgroup haskell-glasses nil
  "Display haskell code scholastic."
  :version "0.1"
  :group 'haskell
  :prefix 'haskell-glasses)

(defcustom glasses-lambda-p t
  "Display lambda abstraction scholastic."
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-lambda-lambda "λ"
  "Display (\\x -> x) as (λx -> x)."
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-lambda-dot "."
  "Display (\\x -> x) as (\\x . x)."
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defface glasses-lambda-face nil
  "Face to be put on lambda abstraction."
  :group 'haskell-glasses)

(defcustom glasses-arrow-p t
  "Display arrow scholastic."
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-arrow-right "→"
  "Display a -> b as a → b."
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-arrow-left "←"
  "Display a <- b as a ← b."
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-arrow-double-right "⇒"
  "Display C a => a as C a ⇒ a."
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defface glasses-arrow-face nil
  "Face to be put on arrow."
  :group 'haskell-glasses)

(defcustom glasses-equiv-p t
  "Display declaration and equal test scholastic."
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-equiv-decl "≡"
  "Display declaration a = b as a ≡ b."
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-equiv-equal "="
  "Display equal test a == b as a = b."
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-equiv-not-equal "≠"
  "Display equal test a /= b as a ≠ b."
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-equiv-greater-equal "≥"
  "Display equal test a >= b as a ≥ b."
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-equiv-less-equal "≤"
  "Display equal test a <= b as a ≤ b."
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defface glasses-equiv-face nil
  "Face to be put on declaration and equal test."
  :group 'haskell-glasses)

(defcustom glasses-subscript-p t
  "Display index-suffixed identifier scholastic, eg. tt1 as tt₁."
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-subscript-inhibit-mix-case-p t
  "Display mix-cased identifier normal, eq. tT1 as tT1."
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-subscript-allow-trailing-p t
  "Display suffixed index along with identifier glasses, eg. undefined1 as ⊥₁"
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defface glasses-subscript-face nil
  "Face to be put on suffixing index numbers."
  :group 'haskell-glasses)

(defcustom glasses-subscript-height 0.75
  "Height of suffixing index number."
  :group 'haskell-glasses
  :type 'number
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-subscript-raise 0
  "Raise of suffixing index number."
  :group 'haskell-glasses
  :type 'number
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-fun-compose-p t
  "Display function composition scholastic."
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-fun-compose "∘"
  "Display f . g as f ∘ g."
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defface glasses-fun-compose-face nil
  "Face to be put on function composition."
  :group 'haskell-glasses)

(defcustom glasses-logic-p t
  "Display boolean operation scholastic."
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-logic-and "∧"
  "Display A && B as A ∧ B."
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-logic-or "∨"
  "Display A || B as A ∨ B."
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-logic-not "¬"
  "Display not A as ¬A."
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defface glasses-logic-face nil
  "Face to be put on boolean operation."
  :group 'haskell-glasses)

(defcustom glasses-bottom-p t
  "Display bottom scholastic"
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

(defface glasses-bottom-face nil
  "Face to be put on bottom."
  :group 'haskell-glasses)

(defcustom glasses-user-defined-glasses nil
  "Display user-defined names scholastic."
  :group 'haskell-glasses
  :type '(alist :key-type (string :tag "Name")
                :value-type (group (string :tag "Glass") (boolean :tag "Infix operator P" :value t) (boolean :tag "Allow trailing P")
                                   (boolean :tag "Enable P") (choice :tag "Face"(const :tag "None" nil) face)))
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

(defmacro aif (test conclusion &rest alternatives)
  `(let ((it ,test))
     (if it
         ,conclusion
       ,@alternatives)))

(defmacro list-every (&rest list)
  (when list
    `(aif ,(car list)
          (cons it (list-every ,@(cdr list)))
          (return nil))))

(defmacro awhens (tests &rest body)
  `(block nil
     (let ((them (list-every ,@tests)))
       (when them
         ,@body))))

(defmacro achoose (tests &rest body)
  `(awhen
    (or
     ,@(mapcar (lambda (test)
                 `(awhens ,(if (atom test)
                               `(,test)
                             test) them)) tests))
    ,@body))

(defmacro awhile (test &rest body)
  (let ((break (gensym "wb"))
        (continue (gensym "wc")))
    `(flet ((break (&optional res) (return-from ,break res))
            (continue () (return-from ,continue)))
       (block ,break
         (while ,test
           (block ,continue
             ,@body))))))

(defmacro while-search (regex lim bw &rest body)
  (let ((max (gensym "mx")))
    `(let ((,max 0))
       (awhile (and
                (,(if bw #'re-search-backward #'re-search-forward) ,regex ,lim t)
                (,(if bw #'> #'<=) (point) ,lim)
                (<= ,max (buffer-size)))
               (setq ,max (1+ ,max))
               ,@body))))

(defun symbolize (&rest things)
  (flet ((ensure-string (thing)
                        (cond  ((symbolp thing) (symbol-name thing))
                               ((numberp thing) (number-to-string thing))
                               ((characterp thing) (char-to-string thing))
                               ((stringp thing) thing)
                               (t (symbol-name (gensym))))))
    (intern (apply #'concat (mapcar #'ensure-string things)))))

(defun haskell-glasses-make-user-glasses-symbol (name)
  (symbolize "glasses-" name))

;;; Glasses overlay

(defvar haskell-glasses-predefined-list
  `((glasses-user-defined-glasses nil)))

(defun haskell-glasses-after-change-function (beg end len)
  (haskell-glasses-mode 1)
  (remove-hook 'after-change-functions #'haskell-glasses-after-change-function t))

(defun haskell-glasses-fix-overlay-cursor (overlay after beg end &optional length)
  (if after (haskell-glasses-mode 1)
    (haskell-glasses-mode -1)
    (add-hook 'after-change-functions #'haskell-glasses-after-change-function nil t)))

(defun haskell-glasses-set-overlay-properties ()
  "Set properties of glasses overlays.
Consider current setting of user variables."
  (flet ()
    (dolist (pg haskell-glasses-predefined-list)
      (put (car pg) 'face (cadr pg))
      (put (car pg) 'insert-in-front-hooks
           (list #'haskell-glasses-fix-overlay-cursor)))
    (dolist (io glasses-user-defined-glasses)
      (let ((gls (haskell-glasses-make-user-glasses-symbol (car io))))
        (put gls 'face (nth 5 io))
        (put gls 'insert-in-front-hooks
             (list #'haskell-glasses-fix-overlay-cursor))))))

(defun haskell-glasses-overlay-p (overlay)
  "Return whether OVERLAY is an overlay of haskell glasses mode."
  (let ((cat (overlay-get overlay 'category))) 
    (or (assoc cat haskell-glasses-predefined-list)
        (memq cat (mapcar (lambda (io) (haskell-glasses-make-user-glasses-symbol (car io))) glasses-user-defined-glasses)))))

(defun haskell-glasses-make-overlay (beg end category)
  "Create and return scholastic overlay over the region from BEG to END.
CATEGORY is the overlay category."
  (let ((overlay (make-overlay beg end)))
    (overlay-put overlay 'category category)
    overlay))

;;; Glasses regexp

(defconst | "\\|")
(defconst \( "\\(")
(defconst \) "\\)")
(defconst \(?: "\\(?:" )
(defun \( (&rest rs) (apply #'concat \( rs))
(defun \(?: (&rest rs) (apply #'concat \(?: rs))

(defconst <id (\(?: "^" | "[^[:alnum:]'_]" \)))
(defconst id> (\(?: "[^[:alnum:]'_]" | "$" \)))
(defconst <op (\(?: "^" | "[^[:punct:]]" | "[]}()_'\"|]" \)))
(defconst op> (\(?: "[^[:punct:]]" | "[[{()_'\"|]" | "$" \)))

(defconst cid (\(?: "[[:upper:]][[:alnum:]_']*"  \) ))
(defconst mid (\(?: \(?: cid  "[.]" \) "*" \) ))

(defconst id1 (\(?: <id \( \(?: "[[:lower:]]+" | "[[:upper:]]+" \)
               "'*" \( "[[:digit:]]+" \) "'*" \) id> \)))
(defconst id2 (\(?: <id \( \(?: "[[:alpha:]_]+" \)
               "'*" \( "[[:digit:]]+" \) "'*" \) id> \)))

(defun iop (opreg)
  (\(?: <op \( mid \( (regexp-quote opreg) \) \) op> \)))

(defun vid (varreg trailing-blanks-p trailing-prime-or-subscript-p)
  (\(?: <id \( mid \( (regexp-quote varreg) \)
   (when trailing-prime-or-subscript-p "[0-9']*") \)
   (if trailing-blanks-p (\("[[:blank:]]+"\)) id>) \)))

(defconst lncmt
  ( \( "--" \(?: "[-[:alnum:][:blank:](){}|;_`'\",]" | "\\[" | "\\]" \) ".*" \) ))

;;; Glasses skips

(defvar haskell-glasses-skip-list nil)
(defun haskell-glasses-skip-list (&optional lim)
  (labels ((escape-p (pos)
              (let ((sls 0))
                (while (and (<= sls pos) (char-equal ?\\ (char-before (- pos sls))))
                  (setq sls (1+ sls)))
                (oddp sls)))
           (skip-quo (quo)
             (with-save
              (while-search quo (point-max) nil
                (unless (escape-p (1- (point))) 
                  (return (point))))
              (return (point-max))))
           (skip-par (opn cls)
             (with-save
              (while-search (\( opn \) | \( cls \)) (point-max) nil
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
     (let ((r ( \( "\"" \)
                | \( "{-" \)
                | lncmt
                | "[^[:alnum:]_']" \( "\'" \)
                | \( "^\'" \)
                | \( "^#.*$"\)
                ))
           (skips nil)
           (lim (or lim (point-max))))
       (while-search r lim nil
         (achoose (((match-beginning 1) (skip-str))
                   ((match-beginning 2) (skip-cmt))
                   ((match-beginning 3) (match-end 3))
                   ((or (match-beginning 4) (match-beginning 5)) (skip-chr))
                   ((match-beginning 6) (match-end 6)))
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
        (args ( \( "(" \) | \( "\\[" \) | \( "{" \)
                | \(?: (iop "->") \) ;Hey! I'm here.
                | "[#@~._'\"]" | ")" | "\\]" | "}"
                | \( "[[:punct:]]" \)))
        (skips (remove-if (lambda (skip)
                            (or (< (cadr skip) pos) (< lim (car skip))))
                          haskell-glasses-skip-list)))
    (labels ((skip-par (o c)
                (with-save
                 (while-search (\( (regexp-quote o) \) | \( (regexp-quote c) \)) 
                               lim nil 
                   (achoose (((match-beginning 1) (match-end 1))
                             ((match-beginning 2) (match-end 2)))
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
       (while-search args lim nil
         (achoose (((match-beginning 1) (match-end 1))
                   ((match-beginning 2) (match-end 2))
                   ((match-beginning 3) (match-end 3))
                   ((match-beginning 4) (match-end 4))
                   ((match-beginning 5) (match-end 5))
                   ((match-beginning 6) (match-end 6)))
                  (aif (haskell-glasses-skip-glasses-p (car it) (cadr it))
                     (goto-char (1- (cadr it)))
                     (when (match-beginning 6) (return))
                     (achoose (((match-beginning 1) (skip-tpl))
                               ((match-beginning 2) (skip-lst))
                               ((match-beginning 3) (skip-rcd)))
                      (goto-char (1- (cadr it))))
                     (achoose (((match-beginning 4) (match-end 4))
                               ((match-beginning 5) (match-end 5)))
                      (return it)))))))))

;;; Glasses makers

(defmacro haskell-glasses-make-glasses (mat tgl-p makers)
  `(lambda (beg end)
     (when ,tgl-p
       (let ((case-fold-search nil))
         (with-save
          (goto-char beg)
          (while-search ,mat end nil
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
    ((2 (lambda (sb se)
          (goto-char (match-end 1))
          (with-save
           ,@body
           (unless (some #'haskell-glasses-overlay-p (overlays-at sb))
             (let ((os (haskell-glasses-make-overlay sb se ,gls)))
               (overlay-put os 'display (eval ,gls))))))))))

(defmacro haskell-glasses-make-vid-glasses (mat gls tgl-p tbk tps &rest body)
  `(haskell-glasses-make-glasses (vid ,mat ,tbk ,tps) ,tgl-p
    ((2 (lambda (sb se)
          (goto-char (match-end 1))
          (with-save
           ,@body
           (let ((os (haskell-glasses-make-overlay sb se ,gls)))
             (overlay-put os 'display (eval ,gls))))))
     (3 (lambda (sb se)
          (with-save
           ,@body
           (let ((os (haskell-glasses-make-overlay sb se ,gls)))
             (overlay-put os 'display ""))))))))

;;; Glasses displays

(defvar haskell-glasses-display-list nil)

(defun haskell-glasses-display-scholastic (beg end)
  "Make haskell code in the region from BEG to END scholastic."
  (map nil (lambda (f) (funcall f beg end)) haskell-glasses-display-list)
  (dolist (io glasses-user-defined-glasses)
    (let* ((nam (nth 0 io))
           (gls (nth 1 io))
           (iop (nth 2 io))
           (atl (nth 3 io))
           (tgl (nth 4 io))
           (sym (haskell-glasses-make-user-glasses-symbol nam)))
      (when tgl
        (set sym gls)
        (if iop
            (funcall (haskell-glasses-make-iop-glasses nam sym tgl) beg end)
          (funcall (haskell-glasses-make-vid-glasses nam sym tgl nil (and atl glasses-subscript-allow-trailing-p)) beg end))))))

(defun haskell-glasses-display-normal (beg end)
  "Display code in the region from BEG to END to their normal state."
  (setq haskell-glasses-skip-list nil)
  (dolist (o (overlays-in beg end))
    (when (haskell-glasses-overlay-p o)
      (delete-overlay o))))

(defun haskell-glasses-display-change (beg end)
  "After-change function updating haskell glass overlays."
  (let ((beg-line (with-save (goto-char beg)
           (if (re-search-backward "^[^[:space:]\n]" (point-min) t)
               (point)
             (line-beginning-position))))
	(end-line (with-save (goto-char end) (line-end-position))))
    (haskell-glasses-display-normal beg-line end-line)
    (haskell-glasses-display-scholastic beg-line end-line)))

;;; Glasses defines

(defmacro define-haskell-glasses (name mat tgl-p face makers)
  `(setq haskell-glasses-predefined-list
         (pushnew (list ',name ',face) haskell-glasses-predefined-list)
         haskell-glasses-display-list
         (pushnew (haskell-glasses-make-glasses ,mat ,tgl-p ,makers) haskell-glasses-display-list)))

(defmacro define-haskell-iop-glasses (name mat tgl-p face &rest body)
  `(setq haskell-glasses-predefined-list
         (pushnew (list ',name ',face) haskell-glasses-predefined-list)
         haskell-glasses-display-list
         (pushnew (haskell-glasses-make-iop-glasses ,mat ',name ,tgl-p ,@body) haskell-glasses-display-list)))

(defmacro define-haskell-vid-glasses (name mat tgl-p face tbk tps &rest body)
  `(setq haskell-glasses-predefined-list
         (pushnew (list ',name ',face) haskell-glasses-predefined-list)
         haskell-glasses-display-list
         (pushnew (haskell-glasses-make-vid-glasses ,mat ',name ,tgl-p ,tbk (and ,tps glasses-subscript-allow-trailing-p) ,@body) haskell-glasses-display-list)))


;;; Predefined glasses

(define-haskell-iop-glasses glasses-arrow-right         "->"        glasses-arrow-p  glasses-arrow-face)
(define-haskell-iop-glasses glasses-arrow-left          "<-"        glasses-arrow-p  glasses-arrow-face)
(define-haskell-iop-glasses glasses-arrow-double-right  "=>"        glasses-arrow-p  glasses-arrow-face)
(define-haskell-iop-glasses glasses-equiv-equal         "=="        glasses-equiv-p  glasses-equiv-face)
(define-haskell-iop-glasses glasses-equiv-not-equal     "/="        glasses-equiv-p  glasses-equiv-face)
(define-haskell-iop-glasses glasses-equiv-greater-equal ">="        glasses-equiv-p  glasses-equiv-face)
(define-haskell-iop-glasses glasses-equiv-less-equal    "<="        glasses-equiv-p  glasses-equiv-face)
(define-haskell-iop-glasses glasses-equiv-decl          "="         glasses-equiv-p  glasses-equiv-face)
(define-haskell-iop-glasses glasses-logic-and           "&&"        glasses-logic-p  glasses-logic-face)
(define-haskell-iop-glasses glasses-logic-or            "||"        glasses-logic-p  glasses-logic-face)
(define-haskell-vid-glasses glasses-logic-not           "not"       glasses-logic-p  glasses-logic-face    t nil)
(define-haskell-vid-glasses glasses-bottom-undefined    "undefined" glasses-bottom-p glasses-bottom-face nil nil)

(define-haskell-iop-glasses glasses-fun-compose "." glasses-fun-compose-p glasses-fun-compose-face
  (when (re-search-backward ( \( cid \) ) (line-beginning-position) t)
    (let ((pse (match-end 1)))
      (when (and pse (= pse sb))
        (return)))))

(define-haskell-iop-glasses glasses-lambda-lambda "\\" glasses-lambda-p glasses-lambda-face
  (goto-char sb)
  (aif (haskell-glasses-find-lamb-dot se (point-max))
       (let  ((os (haskell-glasses-make-overlay (car it) (cadr it) 'glasses-lambda-lambda)))
         (overlay-put os 'display glasses-lambda-dot))
       (return)))

(define-haskell-glasses glasses-subscript (if glasses-subscript-inhibit-mix-case-p id1 id2)
  glasses-subscript-p glasses-subscript-face
  ((2 (lambda (sb se)
        (goto-char (match-end 1))
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