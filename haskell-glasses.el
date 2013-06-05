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

(defcustom glasses-append-p t
  "Display append scholastic"
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-append "⊕"
  "Display ++ as ⊕"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defface glasses-append-face nil
  "Face to be put on append."
  :group 'haskell-glasses)

(defcustom glasses-ellipsis-p t
  "Display append scholastic"
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-ellipsis "…"
  "Display .. as …"
  :group 'haskell-glasses
  :type 'string
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defface glasses-ellipsis-face nil
  "Face to be put on append."
  :group 'haskell-glasses)

(defcustom glasses-allow-prime-and-number-suffix-p t
  "Display suffixing prime and number along with identifier glasses, eg. undefined1' as ⊥₁'"
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-hide-module-name-p t
  "Display glasses but hide prefixing module name, eg. Prelude.undefined as ⊥"
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-semantic-glasses-p t
  "Display glasses according to their importing modules, eg. only Set.`union` as ∪"
  :group 'haskell-glasses
  :type 'boolean
  :set 'haskell-glasses-custom-set
  :initialize 'custom-initialize-default)

(defcustom glasses-user-defined-glasses 
  '(("`union`" "∪" t nil t "Data.Set" t nil)
    ("`intersection`" "∩" t nil t "Data.Set" t nil)
    ("`isSubsetOf`" "⊆" t nil t "Data.Set" t nil)
    ("`isProperSubsetOf`" "⊂" t nil t "Data.Set" t nil)
    ("`member`" "∈" t nil t "Data.Set" t nil)
    ("`notMember`" "∉" t nil t "Data.Set" t nil)
    ("empty" "∅" nil nil t "Data.Set" t nil)
    ("`mappend`" "·" t nil t "Data.Monoid" t nil)
    ("mempty" "e" nil nil t "Data.Monoid" t nil))
  "Display user-defined names scholastic."
  :group 'haskell-glasses
  :type '(alist :key-type (string :tag "Name")
                :value-type (group (string :tag "Glass")
                                   (boolean :tag "Infix operator P" :value t)
                                   (boolean :tag "Allow prime and number suffix P")
                                   (boolean :tag "Hide module name P")
                                   (string :tag "From module")
                                   (boolean :tag "Enable P" :value t)
                                   (choice :tag "Face"(const :tag "None" nil) face)))
  :options '("`union`" "`intersection`" "isSubsetOf" "isProperSubsetOf"
             "`member`" "`notMember`" "empty" "`mappend`" "mempty")
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
       (let ((case-fold-search nil)) (block nil ,@body)))))

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

(defmacro* while-search ((regex &key limit count backward-p) &rest body)
  (let ((max (gensym "mx"))
        (rgx (gensym "rx"))
        (ran (gensym "rn"))
        (cnt (gensym "ct")))
    `(let ((,max 0)
           (,rgx ,regex)
           (,ran (or ,limit (if ,backward-p (point-min) (point-max))))
           (,cnt (or ,count (buffer-size))))
       (awhile (and
                (funcall (if ,backward-p #'re-search-backward #'re-search-forward) ,rgx ,ran t)
                (funcall (if ,backward-p #'> #'<=) (point) ,ran)
                (< ,max ,cnt))
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
        (put gls 'face (nth 7 io))
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

(defconst cid (\(?: "[[:upper:]][[:alnum:]_']*"  \)))
(defconst mid (\(?: \(?: cid  "\\." \) "*" \)))

(defconst id1 (\(?: <id \( \(?: "[[:lower:]]+" | "[[:upper:]]+" \)
               \(?: \( "[[:digit:]]+" \) "'*" | "'*" \( "[[:digit:]]+" \) \) \) id> \)))
(defconst id2 (\(?: <id \( \(?: "[[:alpha:]_]+" \)
               \(?: \( "[[:digit:]]+" \) "'*" | "'*" \( "[[:digit:]]+" \) \) \) id> \)))

(defun modid (fixed-module)
  (when (and glasses-semantic-glasses-p fixed-module)
    (aif (find-if (lambda (mod)
                      (or (string-equal (car mod) fixed-module)
                          (string-equal (cadr mod) fixed-module)))
                    (haskell-glasses-import-list nil))
         (\(?: \(?: (regexp-quote (nth 0 it)) | (regexp-quote (nth 1 it)) \) "\\." \) (unless (nth 2 it) "?"))
         (\(?: (regexp-quote fixed-module) "\\." \)))))

(defun iop (opreg moduleless-p hide-module-p fixed-module)
  (let ((viop-p (char-equal ?\` (string-to-char opreg))))
    (cond (moduleless-p
           (\(?: <op \( \( (regexp-quote opreg) \) \) op> \)))
          ((or viop-p hide-module-p)
           (let ((opreg (if viop-p (substring opreg 1) opreg))
                 (vbq (if viop-p "`" "")))
             (\(?: <op \( \( (regexp-quote vbq) (or (modid fixed-module) mid) (regexp-quote opreg) \) \) op> \))))
          (t
           (\(?: <op \( (or (modid fixed-module) mid) \( (regexp-quote opreg) \) \) op> \))))))

(defun vid (varreg blanks-p suffix-p moduleless-p hide-module-p fixed-module)
  (let ((blanks (if blanks-p (\( "[[:blank:]]+" \)) id>))
        (prime-or-sub (when suffix-p (\(?: "[0-9]*'*" | "'*[0-9]*" \)))))
    (cond (moduleless-p
           (\(?: <id \( \( (regexp-quote varreg) \) prime-or-sub \) blanks \)))
          (hide-module-p
           (\(?: <id \( \( (or (modid fixed-module) mid) (regexp-quote varreg) \) prime-or-sub \) blanks \)))
          (t
           (\(?: <id \( (or (modid fixed-module) mid) \( (regexp-quote varreg) \) prime-or-sub \) blanks \))))))

(defconst lncmt
  (\( "--" \(?: "[-[:alnum:][:blank:](){}|;_`'\",]" | "\\[" | "\\]" \) ".*" \)))

(defconst !^
  (\(?: "[[:space:]]+" | \(?: "\n[[:space:]]+" \) "*" \)))

(defconst import
  (\(?: "^import"
   \( !^ "qualified" \) "?"
   \(?: !^ \( mid cid \) \)
   \(?: !^ "as" !^ \( mid cid \) \) "?"
   \)))

;;; Glasses imports

(defvar haskell-glasses-import-list nil)

(defun haskell-glasses-import-list (force-p)
  (if (and haskell-glasses-import-list (not force-p))
      haskell-glasses-import-list
    (with-save
     (goto-char (point-min))
     (let ((imports nil))
       (while-search (import)
                     (awhen (match-string-no-properties 2)
                            (let ((org it))
                              (aif (match-string-no-properties 3)
                                   (pushnew (list org it (match-beginning 1)) imports)
                                   (pushnew (list org org (match-beginning 1)) imports)))))
       (setq haskell-glasses-import-list imports)))))

;;; Glasses skips

(defvar haskell-glasses-skip-list nil)
(defun haskell-glasses-skip-list (force-p &optional lim)
  (labels ((escape-p (pos)
              (let ((sls 0))
                (while (and (<= sls pos) (char-equal ?\\ (char-before (- pos sls))))
                  (setq sls (1+ sls)))
                (oddp sls)))
           (skip-quo (quo)
             (with-save
              (while-search (quo)
                (unless (escape-p (1- (point))) 
                  (return (point))))
              (return (point-max))))
           (skip-par (opn cls)
             (with-save
              (while-search ((\( opn \) | \( cls \)))
                (if (match-beginning 2)
                    (return (point))
                  (awhen (skip-par opn cls)
                         (goto-char it))))
              (return (point-max))))
           (skip-str () (skip-quo "\""))
           (skip-chr () (skip-quo "\'"))
           (skip-cmt () (skip-par "{-" "-}")))
    (if (and haskell-glasses-skip-list (not force-p))
        haskell-glasses-skip-list
      (with-save
       (goto-char (point-min))
       (let ((r (\( "\"" \)
                 | \( "{-" \)
                 | \(?: "^" | "[^[:alnum:]_']" \) \( "\'" \) 
                 | lncmt
                 | \( "^#.*$"\)
                 ))
             (skips nil)
             (lim (or lim (point-max))))
         (while-search (r :limit lim)
         (achoose (((match-beginning 1) (skip-str))
                   ((match-beginning 2) (skip-cmt))
                   ((match-beginning 3) (skip-chr))
                   ((match-beginning 4) (match-end 4))
                   ((match-beginning 5) (match-end 5)))
           (goto-char (cadr it))
           (setq skips (pushnew it skips))))
         (setq haskell-glasses-skip-list skips))))))

(defun haskell-glasses-skip-glasses-p (beg end)
  (with-save
   (dolist (area (haskell-glasses-skip-list nil))
     (when (or (and (<= (car area) beg) (< beg (cadr area)))
               (and (< (car area) end) (<= end (cadr area))))
       (return area)))))

(defun haskell-glasses-find-lamb-dot (pos &optional lim)
  (let ((lim (or lim (point-max)))
        (args (\( "(" \) | \( "\\[" \) | \( "{" \)
               | (iop "->" t nil nil) ;Hey! I'm here.
               | "[#@~._'\"]" | ")" | "\\]" | "}"
               | \( "[[:punct:]]" \)))
        (skips (remove-if (lambda (skip)
                            (or (< (cadr skip) pos) (< lim (car skip))))
                          (haskell-glasses-skip-list nil))))
    (labels ((skip-par (o c)
                (with-save
                 (while-search ((\( (regexp-quote o) \) | \( (regexp-quote c) \)) 
                                :limit lim)
                   (achoose (((match-beginning 1) (match-end 1))
                             ((match-beginning 2) (match-end 2)))
                    (let ((dot it))
                      (aif (haskell-glasses-skip-glasses-p (car dot) (cadr dot))
                           (goto-char (cadr it)) ;no need to look behind
                           (if (match-beginning 2)
                               (return (cadr dot))
                             (awhen (skip-par o c) (goto-char it)))))))
                 (return lim)))
             (skip-tpl () (skip-par "(" ")"))
             (skip-lst () (skip-par "[" "]"))
             (skip-rcd () (skip-par "{" "}")))
      (with-save
       (goto-char pos)
       (while-search (args :limit lim)
         (achoose (((match-beginning 1) (match-end 1))
                   ((match-beginning 2) (match-end 2))
                   ((match-beginning 3) (match-end 3))
                   ((match-beginning 5) (match-end 5))
                   ((match-beginning 6) (match-end 6)))
                  (aif (haskell-glasses-skip-glasses-p (car it) (cadr it))
                     (goto-char (1- (cadr it)))
                     (when (match-beginning 6) (return))
                     (achoose (((match-beginning 1) (skip-tpl))
                               ((match-beginning 2) (skip-lst))
                               ((match-beginning 3) (skip-rcd)))
                      (goto-char (1- (cadr it))))
                     (achoose (((match-beginning 5) (match-end 5)))
                      (return it)))))))))

;;; Glasses makers

(defmacro haskell-glasses-make-glasses (mat tgl-p makers)
  `(lambda (beg end)
     (when ,tgl-p
       (with-save
          (goto-char beg)
          (while-search (,mat :limit end)
            ,@(mapcar
               (lambda (m)
                 `(progn
                    ,@(mapcar
                       (lambda (n)
                         `(let  ((sb (match-beginning ,n))
                                 (se (match-end ,n)))
                            (when (and sb se (not (haskell-glasses-skip-glasses-p sb se))) 
                              (funcall ,(cadr m) sb se))))
                       (if (atom (car m))
                           (list (car m))
                         (car m)))))
               makers))))))

(defmacro haskell-glasses-make-iop-glasses (mat gls tgl-p nom-p hmo-p fmo &rest body)
  `(haskell-glasses-make-glasses (iop ,mat ,nom-p ,hmo-p ,fmo) ,tgl-p
    ((2 (lambda (sb se)
            (goto-char (match-end 1))
            (with-save
             ,@body
             (unless (some #'haskell-glasses-overlay-p (overlays-at sb))
               (let ((os (haskell-glasses-make-overlay sb se ,gls)))
                 (overlay-put os 'display (eval ,gls))))))))))

(defmacro haskell-glasses-make-vid-glasses (mat gls tgl-p blk-p suf-p nom-p hmo-p fmo &rest body)
  `(haskell-glasses-make-glasses (vid ,mat ,blk-p ,suf-p ,nom-p ,hmo-p ,fmo) ,tgl-p
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
           (hmo (nth 4 io))
           (fmo (nth 5 io))
           (tgl (nth 6 io))
           (sym (haskell-glasses-make-user-glasses-symbol nam)))
      (when tgl
        (set sym gls)
        (if iop
            (funcall (haskell-glasses-make-iop-glasses nam sym tgl nil (and hmo glasses-hide-module-name-p) fmo) beg end)
          (funcall (haskell-glasses-make-vid-glasses nam sym tgl nil (and atl glasses-allow-prime-and-number-suffix-p) nil (and hmo glasses-hide-module-name-p) fmo) beg end))))))

(defun haskell-glasses-display-normal (beg end)
  "Display code in the region from BEG to END to their normal state."
  (setq haskell-glasses-skip-list nil
        haskell-glasses-import-list nil)
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

(defmacro* define-haskell-glasses ((name mat face tgl-p) makers)
  `(setq haskell-glasses-predefined-list
         (pushnew (list ',name ',face) haskell-glasses-predefined-list)
         haskell-glasses-display-list
         (pushnew (haskell-glasses-make-glasses ,mat ,tgl-p ,makers) haskell-glasses-display-list)))

(defmacro* define-haskell-iop-glasses ((name mat face tgl-p &key moduleless-p hide-module-p fixed-module) &rest body)
  `(setq haskell-glasses-predefined-list
         (pushnew (list ',name ',face) haskell-glasses-predefined-list)
         haskell-glasses-display-list
         (pushnew (haskell-glasses-make-iop-glasses ,mat ',name ,tgl-p
                                                    ,moduleless-p (and ,hide-module-p glasses-hide-module-name-p) ,fixed-module
                                                    ,@body)
                  haskell-glasses-display-list)))

(defmacro* define-haskell-vid-glasses ((name mat face tgl-p &key tight-with-latter-p allow-suffix-p moduleless-p hide-module-p fixed-module) &rest body)
  `(setq haskell-glasses-predefined-list
         (pushnew (list ',name ',face) haskell-glasses-predefined-list)
         haskell-glasses-display-list
         (pushnew (haskell-glasses-make-vid-glasses ,mat ',name ,tgl-p
                                                    ,tight-with-latter-p (and ,allow-suffix-p glasses-allow-prime-and-number-suffix-p)
                                                    ,moduleless-p (and ,hide-module-p glasses-hide-module-name-p) ,fixed-module
                                                    ,@body)
                  haskell-glasses-display-list)))


;;; Predefined glasses

(define-haskell-iop-glasses (glasses-arrow-right         "->"        glasses-arrow-face  glasses-arrow-p :moduleless-p t))
(define-haskell-iop-glasses (glasses-arrow-left          "<-"        glasses-arrow-face  glasses-arrow-p :moduleless-p t))
(define-haskell-iop-glasses (glasses-arrow-double-right  "=>"        glasses-arrow-face  glasses-arrow-p :moduleless-p t))
(define-haskell-iop-glasses (glasses-equiv-decl          "="         glasses-equiv-face  glasses-equiv-p :moduleless-p t))
(define-haskell-iop-glasses (glasses-ellipsis            ".."         glasses-ellipsis-face  glasses-ellipsis-p :moduleless-p t))

(define-haskell-iop-glasses (glasses-equiv-equal         "=="        glasses-equiv-face  glasses-equiv-p :hide-module-p t))
(define-haskell-iop-glasses (glasses-equiv-not-equal     "/="        glasses-equiv-face  glasses-equiv-p :hide-module-p t))
(define-haskell-iop-glasses (glasses-equiv-greater-equal ">="        glasses-equiv-face  glasses-equiv-p :hide-module-p t))
(define-haskell-iop-glasses (glasses-equiv-less-equal    "<="        glasses-equiv-face  glasses-equiv-p :hide-module-p t))

(define-haskell-iop-glasses (glasses-append              "++"        glasses-append-face  glasses-append-p :hide-module-p t))

(define-haskell-iop-glasses (glasses-logic-and           "&&"        glasses-logic-face  glasses-logic-p :hide-module-p t))
(define-haskell-iop-glasses (glasses-logic-or            "||"        glasses-logic-face  glasses-logic-p :hide-module-p t))
(define-haskell-vid-glasses (glasses-logic-not           "not"       glasses-logic-face  glasses-logic-p :tight-with-latter-p t :hide-module-p t))

(define-haskell-vid-glasses (glasses-bottom-undefined    "undefined" glasses-bottom-face glasses-bottom-p :hide-module-p t))

(define-haskell-iop-glasses (glasses-fun-compose "." glasses-fun-compose-face glasses-fun-compose-p :hide-module-p t)
  (when (re-search-backward ( \( cid \) ) (line-beginning-position) t)
    (let ((pse (match-end 1)))
      (when (and pse (= pse sb))
        (return)))))

(define-haskell-iop-glasses (glasses-lambda-lambda "\\" glasses-lambda-face glasses-lambda-p :moduleless-p t)
  (goto-char sb)
  (aif (haskell-glasses-find-lamb-dot se (point-max))
       (let  ((os (haskell-glasses-make-overlay (car it) (cadr it) 'glasses-lambda-lambda)))
         (overlay-put os 'display glasses-lambda-dot))
       (return)))

(define-haskell-glasses (glasses-subscript (if glasses-subscript-inhibit-mix-case-p id1 id2) glasses-subscript-face glasses-subscript-p)
  (((2 3) (lambda (sb se)
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