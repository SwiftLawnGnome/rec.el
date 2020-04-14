;;; tco.el --- Tail-call optimization -*- lexical-binding: t; -*-
;;
;; Copyright (C) 2020 Zach Shaftel
;;
;; Author: Zach Shaftel <http://github/SwiftLawnGnome>
;; Maintainer: Zach Shaftel <zshaftel@gmail.com>
;; Created: April 14, 2020
;; Modified: April 14, 2020
;; Version: 0.0.1
;; Keywords:
;; Homepage: https://github.com/zach/tco
;; Package-Requires: ((emacs 28.0.50) (cl-lib "0.5"))
;;
;; This file is not part of GNU Emacs.
;;
;;; Commentary:
;;
;;  TODO
;;
;;; Code:

(require 'dash)
(require 'dash-functional)
;; for `cl--expr-depends-p'
(require 'cl-lib)
(require 'macroexp)
(require 'byte-opt)
(eval-when-compile
  (require 'pcase))

(defconst tco--tail-optimizers
  (--map (cons it (intern (format "tco--convert-%s" it)))
         '(and
           condition-case
           if
           let
           let*
           or
           progn
           cond
           ;; the remaining special forms cannot contain a tail call
           ;; prog1
           ;; quote
           ;; setq
           ;; save-restriction
           ;; save-current-buffer
           ;; save-excursion
           ;; unwind-protect
           ;; while
           ;; defconst
           ;; defvar
           ;; function
           ;; inline
           ;; interactive
           ;; catch
           )))

(defun tco--split-end (list)
  "Returns ((butlast LIST) (car (last LIST)))."
  (let (before)
    (while (cdr list)
      (push (pop list) before))
    (list (nreverse before) (car list))))

(defconst tco--special-form-restorers
  (mapcar (-lambda ((special-form . tco-fun))
            (cons tco-fun
                  (lambda (&rest args)
                    (cons special-form args))))
          tco--tail-optimizers))

(defvar tco--retvar nil
  "Dynamically bound during TCO to the name of the variable
assigned to the iteration's return value.")

(defvar tco--expansion-env nil
  "Dynamically bound during TCO to the macroexpansion environment
that processess special forms.")

;; (defvar tco--reserved-bindings nil
;;   "Dynamically bound during TCO to the the variables which were
;;   established by the `clj-loop'.")

(defun tco--convert-let (binds &rest body)
  `(tco--convert-let
    ,binds
    ,@(tco--prognize body)))

(defun tco--convert-let* (binds &rest body)
  `(tco--convert-let*
    ,binds
    ,@(tco--prognize body)))

(defun tco--mexp (form)
  "macroexpand FORM in `tco--expansion-env'.
If it doesn't expand, emit a form that terminates iteration."
  (let ((expanded (macroexpand form tco--expansion-env)))
    (cond
      ;; macroexpanded, return that
      ((not (eq expanded form)) expanded)
      ;; else its a returning form, so set the return var to its value
      ((byte-compile-nilconstp form) ;if it's null, no need to wrap it in (progn FORM nil)
       `(setq ,tco--retvar ,form))
      (t `(tco--convert-progn (setq ,tco--retvar ,form) nil)))))

(defun tco--prognize (forms)
  (if (null forms)
      `((setq ,tco--retvar nil))
    (let (r)
      (while (cdr forms)
        (push (pop forms) r))
      (nreverse (cons (tco--mexp (car forms)) r)))))

(defun tco--convert-progn (&rest forms)
  (let ((p (tco--prognize forms)))
    (if (cdr p)
        (cons 'tco--convert-progn p)
      (car p))))

(defun tco--convert-and (&rest args)
  (cond
    ((null args)
     `(tco--convert-progn (setq ,tco--retvar t) nil))
    ((null (cdr args)) (tco--mexp (car args)))
    (t (-let [(butl last) (tco--split-end args)]
         `(tco--convert-if
           (tco--convert-and ,@butl)
           ,(tco--mexp last))))))

(defun tco--convert-or (&rest args)
  ;; (pcase args
  ;;   (`() `(setq ,tco--retvar nil))
  ;;   (`(,one) (tco--mexp one))
  ;;   ((app clj--split-list-end `(,butl ,last))
  ;;    `(tco--convert-if
  ;;      (setq ,tco--retvar
  ;;            (tco--convert-or ,@butl))
  ;;      nil
  ;;      ,(tco--mexp last))))
  (cond
    ((null args) `(setq ,tco--retvar nil))
    ((null (cdr args)) (tco--mexp (car args)))
    (t (-let [(butl last) (tco--split-end args)]
         `(tco--convert-if
           (setq ,tco--retvar
                 (tco--convert-or ,@butl))
           nil
           ,(tco--mexp last))))))

(defun tco--convert-condition-case (var form &rest handlers)
  `(tco--convert-condition-case
    ,var ,(tco--mexp form)
    ,@(--map (cons (car it)
                   (tco--prognize (cdr it)))
             handlers)))

(defun tco--convert-if (test then &rest else)
  (cond
    ((byte-compile-trueconstp test) (tco--mexp then))
    ((byte-compile-nilconstp test) (apply #'tco--convert-progn else))
    (t `(tco--convert-if ,test
                     ,(tco--mexp then)
                     ,@(tco--prognize else)))))

(defun tco--convert-cond (&rest conds)
  (when conds
    (let ((rescond '(tco--convert-cond)))
      (while conds
        ;; these transformations are done by `byte-optimize-cond', but it makes
        ;; the tco process easier to work with if they're performed here
        (pcase (car conds)
          (`(,test)
            (push `(t ,(apply #'tco--convert-or test
                              (apply #'tco--convert-cond (cdr conds))))
                  rescond)
            (setq conds nil))
          (`(,test . ,forms)
            (if (byte-compile-nilconstp test)
                (setq conds (cdr conds))
              (push (cons test (tco--prognize forms)) rescond)
              (setq conds (unless (byte-compile-trueconstp test) (cdr conds)))))))
      (nreverse rescond))))

(defun tco--make-recur (vars vals extras)
  "Adapted from `cl-psetf'. Always returns t."
  (let ((varlen (length vars))
        (vallen (length vals)))
    (unless (eq varlen vallen)
      (signal 'wrong-number-of-arguments (list varlen vallen))))
  (or (and (null vars) (null extras)) ;; nothing to set, just tell `while' to keep going
      (let* ((zipped (-zip-lists vars vals))
             (p zipped)
             (vs nil)
             (simple t))
        (while (and p simple)
          (-let [(var val) (pop p)]
            (when (cl--expr-depends-p val vs)
              (setq simple nil))
            (push var vs)))
        (if simple
            `(tco--convert-progn
              (setq ,@(apply #'nconc zipped))
              ,@extras t)
          (-let [(r1 . rev) (nreverse zipped)]
            `(tco--convert-progn
              ,(-reduce-from (-lambda (acc (var val))
                               `(setq ,var (prog1 ,val ,acc)))
                             (cons 'setq r1) rev)
               ,@extras
               t))))))

(defun tco--merge-lets (lets forms &optional reserved)
  (let ((continue? t))
    (while (and forms (null (cdr forms)) continue?)
      (pcase (car forms)
        (`(let ,(app clj--normalize-binds binds) . ,inner)
          (if (or (cdr binds)
                  (and binds (memq (caar binds) reserved)))
              (setq continue? nil)
            (setq lets (append lets binds))
            (setq forms inner)))
        (`(let* ,(app clj--normalize-binds binds) . ,inner)
          (if (and reserved
                   (--any? (memq (car it) reserved) binds))
              (setq continue? nil)
            (setq lets (append lets binds))
            (setq forms inner)))
        (_ (setq continue? nil))))
    (cons lets forms)))

(defun tco--merging-let* (lets &rest forms)
  (cons 'tco--merging-let* (tco--merge-lets lets forms)))

(defun tco--unwrap-progns (form &optional fun-to-call)
  "*Completely* flattens all nested progns in FORM into a single sequence of extressions.
Empty progns become nil.

 (progn
   x
   y
   (progn
     (progn l)
     (progn)
     g
     (progn lm a 0 r))
   (progn
     (progn)
     (progn (progn (list 1 2)))))
=> (x y l nil g lm a 0 r nil (list 1 2))"
  (if (not (eq (car-safe form) 'progn))
      (list (if fun-to-call
                (funcall fun-to-call form)
              form))
    (let* ((i 5000) ;; fail-safe
           (ff (append (cdr form) nil))
           (unp ff))
      (while (and unp (> i 0))
        (setq i (1- i))
        (let* ((rrest (cdr unp))
               (ec (tco--unwrap-progns (car unp) fun-to-call)))
          (setcar unp (car ec))
          (setcdr unp (nconc (cdr ec) rrest))
          (setq unp rrest)))
      (when (zerop i)
        (error "oops, `tco--unwrap-progns' infinite looped"))
      ff)))

(defun clj--unwrapping-progn (&rest forms)
  (let ((e (tco--unwrap-progns (cons 'progn forms))))
    (if (cdr e)
        (cons 'clj--unwrapping-progn e)
      (car e))))

(defgroup tco nil
  "Tail call optimization."
  :group 'lisp)

(defcustom tco-cleaning-level 1
  "Determines how much cleanup should be performed post-TCO.
This is primarily for aesthetic macroexpansion."
  :group 'tco
  :type '(choice
          (const 0 :tag "Keep it ugly")
          (const 1 :tag "Prettify")
          (const 2 :tag "Go a little overboard")
          (const 3 :tag "Go nuts (don't choose this)")))

(defun tco--cleanup (form)
  (letrec ((clean
            (lambda (form)
              (pcase form
                (`(and) t)
                (`(,(or 'or 'setq 'cond)) nil)
                (`(,(or 'and 'or) . ,stuff)
                  (if (cdr stuff)
                      (cons (car form) (mapcar clean stuff))
                    (funcall clean (car stuff))))
                (`(progn . ,_)
                  (macroexp-progn (funcall clean-implicit-progn form)))
                (`(if ,test ,then . ,else)
                  `(if ,(funcall maybe-clean test)
                       ,(funcall clean then)
                     ,@(funcall clean-implicit-progn else)))
                (`(let* ,binds . ,forms)
                  (-let [(bs . fs)
                         (if (>= tco-cleaning-level 2)
                             (tco--merge-lets binds forms)
                           (cdr form))]
                    `(let* ,(funcall clean-let-binds bs)
                       ,@(funcall clean-implicit-progn fs))))
                (`(let ,binds . ,forms)
                  `(let ,(funcall clean-let-binds binds)
                     ,@(funcall clean-implicit-progn forms)))
                (`(condition-case ,v ,f . ,handlers)
                  `(condition-case ,v
                       ,(funcall clean f)
                     ,@(--map (cons (car it)
                                    (tco--unwrap-progns (cons 'progn (cdr it)) clean))
                              handlers)))
                (`(setq . ,_) (funcall clean-setq form))
                ((guard (< tco-cleaning-level 2)) form)
                (`(,(or 'save-restriction
                        'save-excursion
                        'save-current-buffer)
                    . ,stuff)
                  `(,(car form) ,@(funcall clean-implicit-progn stuff)))
                (`(,(or 'prog1 'unwind-protect 'while) ,form1 . ,forms)
                  `(,(car form) ,(funcall clean form1)
                     ,@(tco--unwrap-progns (cons 'progn forms) clean)))
                ((guard (< tco-cleaning-level 3)) form)
                (`(,(and (pred symbolp)
                         (pred fboundp)
                         (app special-form-p 'nil))
                    . ,args)
                  (cons (car form) (mapcar clean args)))
                ((and (guard (> tco-cleaning-level 4)) ;secret level for psychopaths
                      `(function (lambda ,(and (pred listp) args) . ,body)))
                 `(function
                   (lambda ,args
                    ,@(tco--unwrap-progns (cons 'progn body) clean))))
                (_ form))))
           (clean-implicit-progn
            (if (> tco-cleaning-level 1)
                (lambda (f)
                  (tco--unwrap-progns (cons 'progn f) clean))
              (-cut mapcar clean <>)))
           (clean-let-binds
            (if (> tco-cleaning-level 1)
                (lambda (bs)
                  (--map (if (consp (cdr-safe it))
                             (list (car it) (funcall clean (cadr it)))
                           it)
                         bs))
              #'identity))
           (clean-setq
            (if (> tco-cleaning-level 2)
                (-lambda ((_ . sqs))
                  (let ((r (list 'setq)))
                    (while sqs
                      (push (pop sqs) r)
                      (push (funcall clean (pop sqs)) r))
                    (nreverse r)))
              #'identity))
           (maybe-clean (if (> tco-cleaning-level 1)
                            clean
                          #'identity)))
    (funcall clean form)))

(defun clj--loop-normalize-1 (forms env)
  "Set up FORMS for TCO."
  (let* (;; number of recurs encountered
         ;; currently this is only used as a boolean flag; when it's zero,
         ;; there was no recursion, so this can just be converted to a let.
         ;; (recurs 0)
         ;; expand every (compiler) macro and replace `clj-recur' with the
         ;; placeholder `clj--loop-recur', which itself is then converted to a
         ;; form that updates RESETTERS and continues the loop
         (newenv `((clj-recur . ,(lambda (&rest args)
                                   ;; (setf recurs (1+ recurs))
                                   (cons 'clj--loop-recur args)))
                   ,@env)))
    (--map (macroexpand-all it newenv) forms)))

;; (defun clj--loop-normalize-2 (body env reserved)
;;   "BODY is already macroexpanded, RESERVED is the initial
;; variables that can't be converted to a setq in the loop."
;;   (-let* (((initextras . body1)
;;            (tco--merge-lets nil body reserved))
;;           (exp (macroexpand-all (macroexp-progn (tco--unwrap-progns body1))
;;                                 `((let* . tco--merging-let*)
;;                                   (clj--unwrapping-progn
;;                                    . ,(lambda (&rest forms)
;;                                         (cons 'progn forms)))
;;                                   ,@env))))
;;     (cons initextras exp)))

(defun tco--collect-loop-lexical-stuff
    (binds skip-recur-vars remove-rebinds?)
  "BINDS are all like (pattern value)
returns (initial-bindings recur-vars destructuring-setqs)"
  (let (all-bindings
        rebinders
        ds-setters)
    (dolist (bind binds)
      (-let* (((expanded &as main . dsbinds)
               (clj--destructure1 (list bind))))
        (push (if (and remove-rebinds?
                       (apply #'eq main))
                  dsbinds
                expanded)
              all-bindings)
        (push (--map (cons 'setq it) dsbinds) ds-setters)
        (if (zerop skip-recur-vars)
            (push (car main) rebinders)
          (setf skip-recur-vars (1- skip-recur-vars)))))
    (list (apply #'append (nreverse all-bindings))
          (nreverse rebinders)
          (apply #'nconc (nreverse ds-setters)))))

(defun tco--perform (resetters ds-setters loop-body previousenv)
  (let* (;; the variable returned by the final macroexpansion
         (tco--retvar (make-symbol "clj-loop-result"))
         (tail-recurs 0)
         (optimized
          ;; macroexpand with the optimizers in effect
          (let ((tco--expansion-env
                 ;; (append tco--tail-optimizers previousenv)
                 `((clj--loop-recur
                    . ,(lambda (&rest args)
                         (setq tail-recurs (1+ tail-recurs))
                         (tco--make-recur resetters args ds-setters)))
                   ,@tco--tail-optimizers
                   ,@previousenv)))
            (tco--mexp loop-body)))
         ;; restore the real special forms
         (restored
          (macroexpand-all
           optimized
           (append tco--special-form-restorers previousenv))))
    ;; return the number of recur calls, return variable and tco'd body
    (list tail-recurs tco--retvar restored)))

(defun tco--tail-some (pred form)
  (pcase form
    (`(and) (funcall pred t))
    (`(if ,_ ,then . ,else)
      (or (tco--tail-some pred then)
          (tco--tail-some pred (-last-item else))))
    ((or `(,(or 'progn 'or 'and) . ,forms)
         `(,(or 'let 'let*) ,_ . ,forms))
     (tco--tail-some pred (-last-item forms)))
    (`(condition-case ,_ ,form . ,handlers)
      (or (tco--tail-some pred form)
          (--some (tco--tail-some pred (-last-item (cdr it))) handlers)))
    (`(cond . ,conds)
      ())
    (_ (funcall pred form))))

(defun clj--loop-expand
    (binds body &optional remove-rebinds? recur-exclude-count)
  (-let* ((envyy macroexpand-all-environment)
          (normal (clj--loop-normalize-1 body envyy))
          ((initbinds recurvars ds-setqs)
           (tco--collect-loop-lexical-stuff
            (clj-->elisp-let-binds binds)
            (or recur-exclude-count 0) remove-rebinds?))
          (doit
           (lambda (forms1)
             (-let* (((_recurs retvar optimized)
                      (tco--perform
                       recurvars ds-setqs
                       (macroexp-progn forms1)
                       envyy))
                     (clean (tco--cleanup optimized)))
               `(let* (,@initbinds ,retvar)
                  (while ,clean)
                  ,retvar))))
          (recurcheck (lambda (x)
                        (eq (car-safe x) 'clj--loop-recur))))
    (if (tco--tail-some recurcheck (car (last normal)))
        (funcall doit normal)
      `(clj-let ,binds . ,body))))

(provide 'tco)
;;; tco.el ends here
