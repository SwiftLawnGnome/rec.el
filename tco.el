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
(require 'cl-lib)
(require 'cl-macs) ; `cl--expr-depends-p'
(require 'macroexp)
(require 'byte-opt)
(eval-when-compile
  (require 'pcase))

(defvar tco--special-form-optimizers
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

(defvar tco--special-form-restorers
  (mapcar (-lambda ((special-form . tco-fun))
            (cons tco-fun
                  (lambda (&rest args)
                    (cons special-form args))))
          tco--special-form-optimizers))

(defvar tco--retvar nil
  "Dynamically bound during TCO to the name of the variable
assigned to the iteration's return value.")

(defvar tco--expansion-env nil
  "Dynamically bound during TCO to the macroexpansion environment
that processess special forms.")

(defvar tco--used-retvar nil
  "Dynamically bound during TCO and set to t when a form returned
  anything but nil.")

(defun tco--convert-let (binds &rest body)
  `(tco--convert-let ,binds ,@(tco--prognize body)))

(defun tco--convert-let* (binds &rest body)
  `(tco--convert-let* ,binds ,@(tco--prognize body)))

(defun tco--mexp (form)
  "macroexpand FORM in `tco--expansion-env'.
If it doesn't expand, emit a form that terminates iteration."
  (unless (byte-compile-nilconstp form)
    (let ((expanded (macroexpand form tco--expansion-env)))
      (if (not (eq expanded form))
          expanded
        (setq tco--used-retvar t)
        `(tco--convert-progn (setq ,tco--retvar ,form) nil)))))

(defun tco--prognize (forms)
  (when forms
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
     (setq tco--used-retvar t)
     `(tco--convert-progn (setq ,tco--retvar t) nil))
    ((null (cdr args)) (tco--mexp (car args)))
    (t (-let [(butl last) (tco--split-end args)]
         `(tco--convert-if
           (tco--convert-and ,@butl)
           ,(tco--mexp last))))))

(defun tco--convert-or (&rest args)
  (when args
    (cond
      ((null (cdr args)) (tco--mexp (car args)))
      (t (setq tco--used-retvar t)
         (-let [(butl last) (tco--split-end args)]
           `(tco--convert-if
             (setq ,tco--retvar
                   (tco--convert-or ,@butl))
             nil
             ,(tco--mexp last)))))))

(defun tco--convert-condition-case (var form &rest handlers)
  `(tco--convert-condition-case
    ,var ,(tco--mexp form)
    ,@(--map (cons (car it)
                   (tco--prognize (cdr it)))
             handlers)))

(defun tco--convert-if (test then &rest else)
  (cond
    ((byte-compile-trueconstp test) (tco--mexp then))
    ((byte-compile-nilconstp test)
     (apply #'tco--convert-progn else))
    (t `(tco--convert-if
         ,test
         ,(tco--mexp then)
         ,@(tco--prognize else)))))

(defun tco--convert-cond (&rest conds)
  (when conds
    (let ((rescond (list 'tco--convert-cond)))
      (while conds
        ;; these transformations are done by `byte-optimize-cond', but it makes
        ;; the tco process easier to work with if they're performed here
        (pcase (car conds)
          (`(,test)
            (push `(t ,(tco--convert-or
                        test
                        (apply #'tco--convert-cond (cdr conds))))
                  rescond)
            (setq conds nil))
          (`(,test . ,forms)
            (if (byte-compile-nilconstp test)
                (setq conds (cdr conds))
              (push (cons test (tco--prognize forms)) rescond)
              (setq conds (unless (byte-compile-trueconstp test) (cdr conds)))))))
      (nreverse rescond))))

(defun tco--make-recur (_name vars vals before after)
  "Adapted from `cl-psetf'. Always returns t."
  (let ((varlen (length vars))
        (vallen (length vals)))
    (unless (eq varlen vallen)
      (signal 'wrong-number-of-arguments (list varlen vallen))))
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
        (let ((resetter
               (if simple
                   `(setf ,@(apply #'nconc zipped))
                 (-let [(r1 . rev) (nreverse zipped)]
                   (-reduce-from (-lambda (acc (var val))
                                   `(setf ,var (prog1 ,val ,acc)))
                                 (cons 'setq r1) rev)))))
          `(progn ,@before ,resetter ,@after t)))))

(defun tco--normalize-binds (binds)
  (--map (pcase it
           (`(,_ ,_) it)
           (`(,s) (list s nil))
           (_ (list it nil)))
         binds))

(defun tco--merge-lets (lets forms &optional reserved)
  (let ((continue? t))
    (while (and forms (null (cdr forms)) continue?)
      (pcase (car forms)
        (`(let ,(app tco--normalize-binds binds) . ,inner)
          (if (or (cdr binds)
                  (and binds (memq (caar binds) reserved)))
              (setq continue? nil)
            (setq lets (append lets binds))
            (setq forms inner)))
        (`(let* ,(app tco--normalize-binds binds) . ,inner)
          (if (and reserved (--any? (memq (car it) reserved) binds))
              (setq continue? nil)
            (setq lets (append lets binds))
            (setq forms inner)))
        (_ (setq continue? nil))))
    (cons lets forms)))

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

(defun tco--unwrap-progns (form &optional fun-to-call)
  "Completely flattens all nested progns in FORM into a single sequence of extressions.
Empty progns become nil. With `tco-cleaning-level' > 1, nil's
before the last form are removed.

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
  (if (and (eq (car-safe form) 'progn)
           (setq form (cdr form)))
      (let* ((mc (mapcan (lambda (x)
                           (tco--unwrap-progns x fun-to-call))
                         form))
             (cc mc))
        (when (> tco-cleaning-level 1)
          (while (cdr cc)
            (if (car cc)
                (setq cc (cdr cc))
              (setcar cc (cadr cc))
              (setcdr cc (cddr cc)))))
        mc)
    (list (if (and form fun-to-call)
              (funcall fun-to-call form)
            form))))

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
                  (funcall clean-implicit-progn form))
                (`(if ,test ,then . ,else)
                  `(if ,(funcall maybe-clean test)
                       ,(funcall clean then)
                     ,@(funcall clean-implicit-progn else)))
                (`(cond . ,conds)
                  (cons 'cond (--map (cons (funcall clean (car it))
                                           (funcall clean-implicit-progn (cdr it)))
                                     conds)))
                (`(let* ,binds . ,forms)
                  (-let [(bs . fs)
                         (if (> tco-cleaning-level 1)
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
                                    (funcall clean-implicit-progn (cdr it)))
                              handlers)))
                (`(setq . ,_) (funcall clean-setq form))
                ((guard (< tco-cleaning-level 2)) form)
                (`(,(or 'save-restriction
                        'save-excursion
                        'save-current-buffer)
                    . ,stuff)
                  `(,(car form) ,@(funcall clean-implicit-progn stuff)))
                (`(,(or 'prog1 'unwind-protect 'while 'catch) ,form1 . ,forms)
                  `(,(car form) ,(funcall clean form1)
                     ,@(funcall clean-implicit-progn forms)))
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
                    ,@(funcall clean-implicit-progn body))))
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
      (--some (tco--tail-some pred (-last-item it)) conds))
    (_ (funcall pred form))))

(defun tco--non-tail-recur-error (name _places args &rest _)
  (error "Attempted to call %s in non-tail position: %s"
         name (cons name args)))

(cl-defstruct
    (tco-recursion-point
      (:copier nil)
      (:constructor nil)
      (:constructor tco-recursion-point
       (name recur-places
             &key
             pre-recur
             post-recur
             non-tail-handler
             tail-handler)))
  "Instructions for how to convert forms starting with the symbol NAME."
  (name nil :type symbol :documentation
        "The name of the form called to recurse.
  This is `tco-recur' in `tco-loop' and `tco-lambda'.")
  (recur-places nil :type list :documentation
                "The set of gv-places to reset to arguments to
  recursive calls.")
  (pre-recur nil :documentation
             "Forms to be executed before each recursive call.")
  (post-recur nil :documentation
              "Forms to be executed after each recursive call.")
  (tail-handler #'tco--make-recur :type function :documentation
                "The function called to convert recursive calls
  in tail position. It's passed five arguments: NAME,
  RECUR-PLACES, the values to set them to, the forms in
  PRE-RECUR, and the forms in POST-RECUR.")
  (non-tail-handler #'tco--non-tail-recur-error :documentation
                    "The function called to convert recursive
  calls in non-tail position. It is called with the same five
  arguments as TAIL-HANDLER. The default signals an error.")
  (temp-name (gensym "recur-point") :type symbol :documentation
             "A temporary symbol used internally to tag calls to
  NAME during TCO."))

;;;###autoload
(defun tco-perform (body &optional env retvar &rest recursion-points)
  "Perform tail-call optimization on BODY."
  (when (tco-recursion-point-p env)
    (push env recursion-points)
    (setq env nil))
  (when (tco-recursion-point-p retvar)
    (push retvar recursion-points)
    (setq retvar (make-symbol "result")))
  (unless recursion-points
    (error "`tco-perform' requires one or more `tco-recursion-point's."))
  (let* ((tco--retvar retvar)
         (tco--used-retvar nil)
         (tco-converted 0)
         (non-tco-converted 0)
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
                            (unless (= (length args) (length places))
                              (error "Wrong number of arguments to %s" name))
                            (setq tco-converted (1+ tco-converted))
                            (funcall thandler name places args pre post))))
                  recursion-points))
         ;; finally, calls each recur point's non-tail-handler on any calls
         ;; which were not in tail position
         (third-pass
          (mapcar (-lambda ([_ name places pre post _ nthandler tempname])
                    (cons tempname
                          (lambda (&rest args)
                            (setq non-tco-converted (1+ non-tco-converted))
                            (funcall nthandler name places args pre post))))
                  recursion-points))
         (tagged (macroexpand-all (macroexp-progn body) (nconc first-pass env)))
         (tco--expansion-env (nconc second-pass tco--special-form-optimizers))
         (expanded (tco--mexp tagged))
         (post-processed (macroexpand-all
                          expanded
                          (nconc third-pass tco--special-form-restorers))))
    (list (if (> tco-cleaning-level 0)
              (tco--cleanup post-processed)
            post-processed)
          tco--retvar
          tco--used-retvar
          tco-converted
          non-tco-converted)))

;;;###autoload
(defun tco-simple-perform (recurname recur-places body &optional env)
  "Invokes `tco-perform' with appropriate arguments for RECURNAME
to be a recursive call rebinding RECUR-PLACES."
  (tco-perform body env (tco-recursion-point recurname recur-places)))

;;;###autoload
(defun tco-make-simple-body (binds expansion-spec &optional origbody is-lambda?)
  "Takes a list of let BINDS (or function arglist, when
IS-LAMBDA?) and a list returned by `tco-perform' and returns (cons
BINDS FINAL-ITERATION-FORM). Simply cons `let*' (or `lambda' or
equivalent) onto it to create the final iteration form. If there
were no recursive tail calls and ORIGBODY is provided, then
returns (cons BINDS ORIGBODY) unchanged, else returns the
aforementioned form regardless."
  (-let [(whileform retvar retvarused? recurcount) expansion-spec]
    (cond
      ((and (zerop recurcount) origbody) `(,binds ,@origbody))
      ((not is-lambda?)
       (let ((rv (if retvarused? (list retvar))))
         `((,@binds ,@rv) (while ,whileform) ,@rv)))
      ((not retvarused?) `(,binds (while ,whileform)))
      (t `(,binds (let (,retvar) (while ,whileform) ,retvar))))))

(defun tco--loop-lexical-stuff (binds &optional only-ds-inits)
  "returns (INITIAL-BINDINGS RECUR-VARS DESTRUCTURING-SETQS)"
  (let (all-bindings rebinders ds-setters)
    (dolist (bind (tco--normalize-binds binds))
      (-let [(expanded &as (main) . dsbinds)
             (apply #'dash--match bind)]
        (push (--map (cons 'setq it) dsbinds) ds-setters)
        (push main rebinders)
        (push (if only-ds-inits
                  dsbinds
                expanded)
              all-bindings)))
    (list (apply #'append (nreverse all-bindings))
          (nreverse rebinders)
          (apply #'append (nreverse ds-setters)))))

;;;###autoload
(defmacro tco-loop (binds &rest body)
  (declare (indent defun))
  (-let* (((initbinds recurvars ds-setters)
           (tco--loop-lexical-stuff binds))
          (recurpoint (tco-recursion-point
                       'tco-recur recurvars
                       :post-recur ds-setters))
          (env macroexpand-all-environment)
          (expansion (tco-perform body env recurpoint))
          ((finalbinds . finalbody)
           (tco-make-simple-body initbinds expansion body)))
    (if finalbinds
        `(let* ,finalbinds ,@finalbody)
      (macroexp-progn finalbody))))

(defun tco--lambda-lexical-stuff (args)
  "Returns (ARGLIST DESTRUCTURING-BINDS)"
  (let (arglist ds-stuff (i 0))
    (dolist (arg args)
      (setq i (1+ i))
      (when (memq arg '(&optional &rest))
        ;; coming soon, hopefully
        (error "%s args are not allowed in `tco-lambda' yet" arg))
      (if (symbolp arg)
          (push arg arglist)
        (let ((as (make-symbol (format "arg%d" i))))
          (push as arglist)
          (push (dash--match arg as) ds-stuff))))
    (list (nreverse arglist)
          (apply #'append (nreverse ds-stuff)))))

(defmacro tco-recur (&rest args)
  (ignore args)
  (error "`tco-recur' called outside of `tco-lambda' or `tco-loop'."))

;;;###autoload
(defmacro tco-lambda (&rest body)
  "`-lambda' with tail-call optimization.

The first argument may be a non-nil symbol, in which case calls
to that symbol in tail-position will be converted, and other
calls remain regular recursive calls. Without a name, `tco-recur'
can be used to recurse, but an error is signaled if it's not in
tail position.

\(fn [NAME] ARGLIST &rest BODY)"
  (declare (indent defun))
  (-let* (((name args body)
           (if (nlistp (car body))
               body
             (cons 'tco-recur body)))
          (boundname nil)
          ((arglist ds) (tco--lambda-lexical-stuff args))
          (recurpoint
           (tco-recursion-point
            name arglist
            :post-recur ds
            :non-tail-handler
            ;; allow non-tail recursive calls when it's named
            (if (eq name 'tco-recur)
                (lambda (&rest args)
                  (error (concat "`tco-recur' called from non-tail position: %s\n"
                                 "Give the `tco-lambda' a name and call that to permit this.")
                         (cons 'tco-recur args)))
              (lambda (&rest args)
                (unless boundname
                  (setq boundname (make-symbol (symbol-name name))))
                `(funcall ,boundname ,@args)))))
          ;; ((whileform retvar recurcount retvarused?)
          ;;  (tco-expand body macroexpand-all-environment recurpoint))
          ;; (finalfun
          ;;  (if (zerop recurcount)
          ;;      `(lambda ,args
          ;;         ,@(if (null ds)
          ;;               body
          ;;             `((let* ,ds ,@body))))
          ;;    `(lambda ,args
          ;;       (let* (,@ds ,retvar)
          ;;         ,whileform
          ;;         ,retvar))))
          (expansion (tco-expand body macroexpand-all-environment recurpoint))
          (finalfun (cons 'lambda (tco-make-body arglist expansion body :lambda))))
    (if boundname
        `(letrec ((,boundname ,finalfun)) ,boundname)
      finalfun)))

(with-eval-after-load 'cl-indent
  ;; `common-lisp-indent-function' (which i use in elisp-mode) indents functions
  ;; with 'defun lisp-indent-function properties exactly like an actual `defun',
  ;; whereas `lisp-indent-function' just indents everything after the first line
  ;; with `lisp-body-indent', which is what we want for named `tco-loop/let's
  (defun tco--call-standard-lisp-indent-function (_path state indent-point &rest _)
    "Make `tco-lambda' and `tco-loop' indent via the standard
`lisp-indent-function' when the buffer's value of that variable
is `common-lisp-indent-function'."
    (lisp-indent-function indent-point state))
  (put 'tco-lambda 'common-lisp-indent-function-for-elisp
       #'tco--call-standard-lisp-indent-function)
  (put 'tco-loop 'common-lisp-indent-function-for-elisp
       #'tco--call-standard-lisp-indent-function))

(provide 'tco)
;;; tco.el ends here
