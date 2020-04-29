;;; rec.el --- Tail-call optimization -*- lexical-binding: t; -*-
;;
;; Copyright (C) 2020 Zach Shaftel
;;
;; Author: Zach Shaftel <http://github/SwiftLawnGnome>
;; Maintainer: Zach Shaftel <zshaftel@gmail.com>
;; Created: April 14, 2020
;; Modified: April 14, 2020
;; Version: 0.0.1
;; Keywords:
;; Homepage: https://github.com/SwiftLawnGnome/rec.el
;;
;; This file is not part of GNU Emacs.
;;
;;; Commentary:
;;
;;  See README.org
;;
;;; Code:

(require 'dash)
(require 'dash-functional)
(require 'cl-macs) ; needed at run time for `cl--expr-depends-p'
(require 'macroexp)
(require 'byte-opt)

(defvar rec--special-form-optimizers
  (--map (cons it (intern (format "rec--convert-%s" it)))
         (list 'and
               'if
               'let
               'let*
               'or
               'progn
               'cond
               ;; arguably condition-case shouldn't be converted, but when
               ;; there's no error, nothing special is done pre or post
               ;; executing the main expression, and the error handlers are
               ;; implicit progns.
               'condition-case
               ;; these special forms aren't converted to preserve the semantics
               ;; of recursion
               ;; 'prog1
               ;; 'save-restriction
               ;; 'save-current-buffer
               ;; 'save-excursion
               ;; 'unwind-protect
               ;; these special forms always return constants
               ;; 'function
               ;; 'quote
               ;; 'defconst
               ;; 'defvar
               ;; 'while
               ;; not converted because it's too tricky
               ;; 'catch
               ;; these are just weird
               ;; 'setq
               ;; 'interactive
               ))
  "Alist mapping special-form names to functions which convert
  tail calls within them.")

(defvar rec--special-form-restorers
  (mapcar (-lambda ((s))
            (--> (intern (format "rec--%s" s)) (cons it it)))
          rec--special-form-optimizers)
  "Alist mapping special-form placeholders to functions which
  restore the original special form.")

(defun rec--split-end (list)
  "Returns ((butlast LIST) . (car (last LIST)))."
  (let (before)
    (while (cdr list)
      (push (pop list) before))
    (cons (nreverse before) (car list))))

(defvar rec--retvar nil
  "Dynamically bound during TCO to the name of the variable
assigned to the iteration's return value.")

(defvar rec--expansion-env nil
  "Dynamically bound during TCO to the macroexpansion environment
that processess special forms.")

(defvar rec--used-retvar nil
  "Dynamically bound during TCO and set to t when a form returned
anything but nil.")

(defun rec--mexp (form)
  "macroexpand FORM in `rec--expansion-env'.
If it doesn't expand, emit a form that terminates iteration
returning the value of FORM."
  (unless (byte-compile-nilconstp form)
    (let ((expanded (macroexpand form rec--expansion-env)))
      (if (not (eq expanded form))
          expanded
        (setq rec--used-retvar t)
        `(rec--progn (setq ,rec--retvar ,form) nil)))))

(defun rec--convert-forms (forms)
  (when forms
    (let (r)
      (while (cdr forms)
        (push (pop forms) r))
      (nreverse (cons (rec--mexp (car forms)) r)))))

(defun rec--convert-let (binds &rest body)
  `(rec--let ,binds ,@(rec--convert-forms body)))

(defun rec--convert-let* (binds &rest body)
  `(rec--let* ,binds ,@(rec--convert-forms body)))

(defun rec--convert-progn (&rest forms)
  (let ((p (rec--convert-forms forms)))
    (cons 'rec--progn p)))

(defun rec--convert-and (&rest args)
  (cond
    ((null args)
     (setq rec--used-retvar t)
     `(rec--progn (setq ,rec--retvar t) nil))
    ((null (cdr args)) (rec--mexp (car args)))
    (t (-let [(butl . last) (rec--split-end args)]
         `(rec--if (rec--and ,@butl) ,(rec--mexp last))))))

(defun rec--convert-or (&rest args)
  (cond
    ((null args) nil)
    ((null (cdr args)) (rec--mexp (car args)))
    (t (setq rec--used-retvar t)
       (-let [(butl . last) (rec--split-end args)]
         `(rec--if
           (setq ,rec--retvar
                 (rec--or ,@butl))
           nil
           ,(rec--mexp last))))))

(defun rec--convert-condition-case (var form &rest handlers)
  `(rec--condition-case
    ,var ,(rec--mexp form)
    ,@(--map (cons (car it)
                   (rec--convert-forms (cdr it)))
             handlers)))

(defun rec--convert-if (test then &rest else)
  (cond
    ((byte-compile-trueconstp test) (rec--mexp then))
    ((byte-compile-nilconstp test)
     (apply #'rec--convert-progn else))
    (t `(rec--if
         ,test
         ,(rec--mexp then)
         ,@(rec--convert-forms else)))))

(defun rec--convert-cond (&rest conds)
  (let ((resconds nil))
    (while conds
      (-let [(test . forms) (car conds)]
        ;; these optimizations are done by `byte-optimize-cond' but it can make
        ;; tco a bit easier if it's done here
        (cond
          ((null forms)
           (push `(t ,(rec--convert-or
                       test
                       (apply #'rec--convert-cond (cdr conds))))
                 resconds)
           (setq conds nil))
          ((byte-compile-nilconstp test) (setq conds (cdr conds)))
          (t (push (cons test (rec--convert-forms forms)) resconds)
             (setq conds (unless (byte-compile-trueconstp test) (cdr conds)))))))
    (when resconds
      (cons 'rec--cond (nreverse resconds)))))

(defun rec--make-recur (name vars vals before after)
  "The default `tco-recursion-point' :tail-handler.
Rebinds VARS to VALS and returns t so that iteration continues.
Adapted from `cl-psetf'."
  (unless (= (length vars) (length vals))
    (error "Wrong number of arguments to %s" name))
  (or (and (null vars) (null before) (null after)) ; nothing to set, just tell
                                                   ; `while' to keep going
   (let* ((zipped (-zip-lists vars vals))
          (p zipped)
          (vs nil)
          (simple t))
     (while (and p simple)
       (-let [(var val) (pop p)]
         (when (cl--expr-depends-p val vs)
           (setq simple nil))
         (push var vs)))
     (let ((resetters
            (if simple
                (--map `(setf ,@it) zipped)
              (-let [(r1 . rev) (nreverse zipped)]
                (list (-reduce-from (-lambda (acc (var val))
                                      `(setf ,var (prog1 ,val ,acc)))
                                    (cons 'setf r1) rev))))))
       `(rec--progn ,@before ,@resetters ,@after t)))))

(defun rec--normalize-binds (binds)
  (--map (if (or (cdr-safe it) (vectorp it))
             it
           (list (or (car-safe it) it) nil))
         binds))

(defun rec--unwrap-progns (forms &optional progn-name fun-to-call)
  "Completely flattens all nested progns in FORM into a single sequence of extressions.
Empty progns become nil. nil's before the last form are removed.
This function is used for improving readability of macroexpansion.

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
     (progn
       (progn (list 1 2))
       (progn))))
=> (x y l g lm a 0 r (list 1 2) nil)"
  (letrec ((pn (or progn-name 'progn))
           (descend
            (lambda (form)
              (if (and (eq (car-safe form) pn)
                       (setq form (cdr form)))
                  (let* ((mc (mapcan descend form))
                         (cc mc))
                    (while (cdr cc)
                      (if (car cc)
                          (setq cc (cdr cc))
                        (setcar cc (cadr cc))
                        (setcdr cc (cddr cc))))
                    mc)
                (list (if (and form fun-to-call)
                          (funcall fun-to-call form)
                        form))))))
    (cond
      ;; only if we're not compiling
      ((not byte-compile-current-file)
       (funcall descend (cons pn forms)))
      (fun-to-call (mapcar fun-to-call forms))
      (t forms))))

(defun rec--progn (&rest args)
  (macroexp-progn (rec--unwrap-progns args 'rec--progn)))

(defun rec--if (test then &rest else)
  `(if ,test
       ,then
     ,@(rec--unwrap-progns else 'rec--progn)))

(defun rec--and (&rest tests)
  (cond
    ((null tests))
    ((null (cdr tests)) (car tests))
    (t (cons 'and tests))))

(defun rec--or (&rest tests)
  (cond
    ((null tests) nil)
    ((null (cdr tests)) (car tests))
    (t (cons 'or tests))))

(defun rec--cond (&rest conds)
  (let* ((res nil))
    (while conds
      (-let [(test . forms) (car conds)]
        (unless (byte-compile-nilconstp test)
          (push (cons test (rec--unwrap-progns forms 'rec--progn)) res))
        (setq conds (unless (byte-compile-trueconstp test) (cdr conds)))))
    (when res
      (cons 'cond (nreverse res)))))

(defun rec--condition-case (errvar form &rest handlers)
  `(condition-case ,errvar
       ,form
     ,@(mapcar (-lambda ((err . forms))
                 (cons err (rec--unwrap-progns forms 'rec--progn)))
               handlers)))

(defun rec--restore-let (letname binds body)
  `(,letname ,binds ,@(rec--unwrap-progns body 'rec--progn)))

(defun rec--let (binds &rest body)
  (rec--restore-let 'let binds body))

(defun rec--let* (binds &rest body)
  (rec--restore-let 'let* binds body))

(defun rec--non-tail-recur-error (name _places args &rest _)
  (error "Attempted to call %s in non-tail position: %s"
         name (cons name args)))

(cl-defstruct (rec-recursion-point
                (:copier nil)
                (:constructor nil)
                (:constructor rec-recursion-point
                 (name recur-places
                       &key
                       pre-recur
                       post-recur
                       non-tail-handler
                       tail-handler)))
  "Instructions for `rec-perform' to convert forms starting with
the symbol NAME."
  (name nil :type symbol :documentation
        "The name of the form called to recurse.")
  (recur-places nil :type list :documentation
                "The set of gv-places to reset to arguments to
  recursive calls.")
  (pre-recur nil :documentation
             "Forms to be executed before each recursive call.")
  (post-recur nil :documentation
              "Forms to be executed after each recursive call.")
  (tail-handler #'rec--make-recur :type function :documentation
                "The function called to convert recursive calls
  in tail position. It's passed five arguments: NAME,
  RECUR-PLACES, the values to set them to, the forms in
  PRE-RECUR, and the forms in POST-RECUR.")
  (non-tail-handler #'rec--non-tail-recur-error :documentation
                    "The function called to convert recursive
  calls in non-tail position. It is called with the same five
  arguments as TAIL-HANDLER. The default signals an error.")
  (temp-name (gensym "recur-point") :type symbol :documentation
             "A temporary symbol used internally to tag calls to
  NAME during TCO."))

;;;###autoload
(defun rec-perform (body &optional env retvar &rest recursion-points)
  "Perform tail-call optimization on BODY."
  (when (rec-recursion-point-p env)
    (push env recursion-points)
    (setq env nil))
  (when (rec-recursion-point-p retvar)
    (push retvar recursion-points)
    (setq retvar (make-symbol "result")))
  (if (not recursion-points)
      (list (macroexp-progn body) retvar nil 0)
    (let* ((rec--retvar retvar)
           (rec--used-retvar nil)
           (tco-converted 0)
           ;; first expand all macros in BODY and replace all RECURSION-POINTS
           ;; with placeholder forms that are processed in the second pass
           (first-pass
            (mapcar (-lambda ([_ name _ _ _ _ _ tempname])
                      (cons name (lambda (&rest args)
                                   (cons tempname args))))
                    recursion-points))
           ;; convert all tagged recur points in tail position into forms which
           ;; update their places and continue the while loop
           (second-pass
            (mapcar (-lambda ([_ name places pre post thandler _ tempname])
                      (cons tempname
                            (lambda (&rest args)
                              (setq tco-converted (1+ tco-converted))
                              (funcall thandler name places args pre post))))
                    recursion-points))
           ;; finally, calls each recur point's non-tail-handler on any calls
           ;; which were not in tail position
           (third-pass
            (mapcar (-lambda ([_ name places pre post _ nthandler tempname])
                      (cons tempname
                            (lambda (&rest args)
                              (funcall nthandler name places args pre post))))
                    recursion-points))
           (tagged (macroexpand-all (macroexp-progn body) (nconc first-pass env)))
           (rec--expansion-env (nconc second-pass rec--special-form-optimizers))
           (expanded (rec--mexp tagged))
           (post-processed (macroexpand-all
                            expanded
                            (nconc third-pass rec--special-form-restorers))))
      (list post-processed
            rec--retvar
            rec--used-retvar
            tco-converted))))

(defun rec-make-simple-body
    (binds expansion-spec &optional each-recur origbody is-lambda?)
  "Takes a list of let BINDS (or function arglist, when
IS-LAMBDA?) and a list returned by `rec-perform' and
returns (BINDS . FINAL-ITERATION-FORM). Simply cons `let*' (or
`lambda' or equivalent) onto it to create the final iteration
form. EACH-RECUR is a list of additional forms executed in the
body of the resulting `while' loop. If there were no recursive
tail calls and ORIGBODY is provided, then returns (cons BINDS
ORIGBODY) unchanged, else returns the aforementioned form
regardless."
  (-let [(whileform retvar retvarused? recurcount) expansion-spec]
    (cond
      ((and (zerop recurcount) origbody) `(,binds ,@origbody))
      ((not is-lambda?)
       `((,@binds ,@(if retvarused? `((,retvar nil))))
         (while ,whileform ,@each-recur)
         ,@(if retvarused? (list retvar))))
      ((not retvarused?) `(,binds (while ,whileform ,@each-recur)))
      (t `(,binds (let (,retvar)
                    (while ,whileform ,@each-recur)
                    ,retvar))))))

(defmacro rec (&rest args)
  "Rebind all recursion variables to each of ARGS and recurse.
Must be called within the body of `rec-lambda' or `rec-let'."
  (ignore args)
  (error "`rec' called outside of `rec-lambda' or `rec-let'."))

(defun rec--let-lexical-stuff (binds &optional sym-prefix)
  "returns (INITIAL-BINDINGS RECUR-VARS DESTRUCTURING-SETQS)"
  (let ((i 0)
        (fmt (concat (or sym-prefix "bind") "%d"))
        all-bindings rebinders ds-setters)
    (dolist (bind (if (vectorp binds)
                      (list binds)
                    (rec--normalize-binds binds)))
      (setq i (1+ i))
      (-let* ((b (elt bind 0))
              (v (elt bind 1))
              ((expanded &as (main) . dsbinds)
               ;; KLUDGE dash is clever enough to turn simple destructuring like
               ;; ((first) list) into (first (car list)), so a temporary var is
               ;; needed to ensure destructuring happens upon each recursion
               (if (or (symbolp b) (listp bind))
                   (list (list b v))
                 (let ((s (make-symbol (format fmt i))))
                   (cons (list s v) (dash--match b s))))))
        (push expanded all-bindings)
        (if (listp bind)
            (push (cons 'setq (apply #'append expanded)) ds-setters)
          (push main rebinders)
          (when ds-setters
            (push (cons 'setq (apply #'append dsbinds)) ds-setters)))))
    (list (apply #'append (nreverse all-bindings))
          (nreverse rebinders)
          (nreverse ds-setters))))

(defun rec--let-expand (name vars body)
  (-let* (((initbinds recurvars ds-setters)
           (rec--let-lexical-stuff vars))
          (recurpoint (rec-recursion-point name recurvars))
          (env macroexpand-all-environment)
          (expansion (rec-perform body env recurpoint))
          ((finalbinds . finalbody)
           (rec-make-simple-body initbinds expansion ds-setters body)))
    (if finalbinds
        `(let* ,finalbinds ,@finalbody)
      (macroexp-progn finalbody))))

;;;###autoload
(defmacro rec-let (vars &rest body)
  "Bind variables according to VARS in sequence and eval BODY.

VARS is a list of 0 or more LETVARs and RECURVARs. LETVARs take
the form of regular `let' bindings, and RECURVARs take the form
[BIND VALUE]. Optionally, VARS can be just one single RECURVAR.
All can contain `-let' style destructuring. Within body,
`rec' (or NAME, if provided) can be invoked in tail position
to recurse, rebinding each RECURVAR to the cooresponding
argument, then updating destructuring and LETVARS.

\(fn [NAME] VARLIST &rest BODY)"
  (declare (indent defun)
           (debug ([&optional symbolp]
                   [&or (vector [&rest [sexp form]])
                        (&rest [&or (sexp form) sexp
                                    (vector sexp form)])]
                   body)))
  (if (sequencep vars)
      (rec--let-expand 'rec vars body)
    (rec--let-expand vars (car body) (cdr body))))

(defun rec--lambda-lexical-stuff (args)
  "Returns (ARGLIST RECURVARS DESTRUCTURING-BINDS)"
  (let (arglist recurvars ds-stuff)
    (--each-indexed args
      (if (symbolp it)
          (progn
            (push it arglist)
            (unless (memq it '(&optional &rest))
              (push it recurvars)))
        (-let* ((s (make-symbol (format "arg%d" it-index)))
                (matched (dash--match it s)))
          (push s arglist)
          (push s recurvars)
          (push matched ds-stuff))))
    (list (nreverse arglist)
          (nreverse recurvars)
          (apply #'append (nreverse ds-stuff)))))

(defun rec--lambda-expand (recurname body)
  (-let* ((args (car body))
          ((decls . body) (macroexp-parse-body (cdr body)))
          (rec-used nil)
          ((arglist rvars ds) (rec--lambda-lexical-stuff args))
          (non-tail (when recurname
                      (lambda (_name _recs vals &rest _args)
                        (setq rec-used t)
                        `(funcall ,recurname ,@vals))))
          (recurpoint
           (apply #'rec-recursion-point
                  (or recurname 'rec) rvars
                  ;; :post-recur (--map (cons 'setq it) ds)
                  ;; allow non-tail recursive calls only when it's named
                  (when non-tail
                    (list :non-tail-handler non-tail))))
          (env macroexpand-all-environment)
          ((expansion &as _ _ _ recurcount) (rec-perform body env recurpoint))
          ((finalargs . finalbody)
           (if (and (zerop recurcount) rec-used)
               ;; TODO handle the case of only non-tail self calls better
               ;; this is ugly
               (cons arglist
                     (macroexp-unprogn
                      (macroexpand-all
                       (macroexp-progn body)
                       `((,recurname
                          . ,(lambda (&rest args)
                               `(funcall ,recurname ,@args)))
                         ,@env))))
             (rec-make-simple-body arglist expansion
                                   (--map `(setq ,@it) ds) body :lambda))))

    (list (and rec-used recurname)
          finalargs
          (append decls
                  (if ds
                      `((let* ,ds ,@finalbody))
                    finalbody)))))

;;;###autoload
(defmacro rec-lambda (&rest body)
  "`-lambda' with tail-call optimization.

If the first argument is an arglist, `rec' can be used to
recurse, but an error is signaled if it's not in tail position.
The first argument may also be a non-nil symbol NAME, in which
case the resulting function is bound to NAME via `letrec'. Calls
in tail position will be converted, and other calls remain
regular recursive calls. Any &optional and &rest arguments must
be supplied on each tail-recursive call.

\(fn [NAME] ARGLIST &rest BODY)"
  (declare (indent defun) (doc-string 2)
           (debug (&define [&optional symbolp] sexp lambda-doc
                           [&optional ("interactive" interactive)]
                           def-body)))
  (-let* (((boundname args fbody)
           (rec--lambda-expand (if (nlistp (car body)) (pop body)) body))
          (func `(lambda ,args ,@fbody)))
    (if boundname
        `(letrec ((,boundname ,func)) ,boundname)
      func)))

;; `common-lisp-indent-function' indents functions with 'defun
;; lisp-indent-function symbol properties exactly like an actual `defun',
;; whereas `lisp-indent-function' just indents everything after the first line
;; with `lisp-body-indent', which is what we want for named `rec-let/lambda'.
(defun rec--call-standard-lisp-indent-function (_path state indent-point &rest _)
  "Make `rec-lambda' and `rec-let' indent via the standard
`lisp-indent-function' when the buffer's value of that variable
is `common-lisp-indent-function'."
  (lisp-indent-function indent-point state))

(put 'rec-let 'common-lisp-indent-function-for-elisp
     #'rec--call-standard-lisp-indent-function)
(put 'rec-lambda 'common-lisp-indent-function-for-elisp
     #'rec--call-standard-lisp-indent-function)

(provide 'rec)
;;; rec.el ends here
