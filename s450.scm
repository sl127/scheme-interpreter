;;; file: s450.scm
;;;
;;; Metacircular evaluator from chapter 4 of STRUCTURE AND
;;; INTERPRETATION OF COMPUTER PROGRAMS (2nd edition)
;;;
;;; Modified by kwn, 3/4/97
;;; Modified and commented by Carl Offner, 10/21/98 -- 10/12/04
;;;
;;; This code is the code for the metacircular evaluator as it appears
;;; in the textbook in sections 4.1.1-4.1.4, with the following
;;; changes:
;;;
;;; 1.  It uses #f and #t, not false and true, to be Scheme-conformant.
;;;
;;; 2.  Some function names were changed to avoid conflict with the
;;; underlying Scheme:
;;;
;;;       eval => xeval
;;;       apply => xapply
;;;       extend-environment => xtend-environment
;;;
;;; 3.  The driver-loop is called s450.
;;;
;;; 4.  The booleans (#t and #f) are classified as self-evaluating.
;;;
;;; 5.  These modifications make it look more like UMB Scheme:
;;;
;;;        The define special form evaluates to (i.e., "returns") the
;;;          variable being defined.
;;;        No prefix is printed before an output value.
;;;
;;; 6.  I changed "compound-procedure" to "user-defined-procedure".
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 xeval and xapply -- the kernel of the metacircular evaluator
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (xeval exp env)
  (let ((action (or (lookup-action (type-of exp))
                    (lookup-as-variable (type-of exp) env))))
    (cond (action (action exp env))
          ((delayed? exp) (xeval (saved-exp exp) ((saved-env exp))))
          ((eof-object? exp) (exit))
          ((isolated-special-form? exp) exp)
          ((self-evaluating? exp) exp)
          ((variable? exp)
           (let ((value (lookup-variable-value exp env)))
             (if (reference? value)
                 (xeval (saved-exp value) (saved-env value))
                 value)))
          ((application? exp)
           (let ((procedure (xeval (operator exp) env)))
             (xapply procedure
                     (if (user-defined-procedure? procedure)
                         (special-values (operands exp)
                                         env
                                         (procedure-parameters procedure))
                         (list-of-values (operands exp) env)))))
          (else
           (s450error "Unknown expression type -- XEVAL " exp)))))

(define (xapply procedure arguments)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments))
        ((user-defined-procedure? procedure)
         (let ((result (eval-sequence
                        (procedure-body procedure)
                        (xtend-environment
                         (execution-parameters (procedure-parameters procedure))
                         arguments
                         (procedure-environment procedure)))))
           (begin (pop-dynamic)
                  result)))
        (else
         (s450error
          "Unknown procedure type -- XAPPLY " procedure))))

;;; Special arguments----------------------

(define (saved-exp obj)
  (cadr obj))

(define (saved-env obj)
  (caddr obj))

;;user-defined-proc argument evaluation 
(define (special-values exps env parameters)
  (cond ((no-operands? exps) '())
        ((pair? (car parameters))
         (cons ((special-argument (car parameters)) (first-operand exps) env)
               (special-values (rest-operands exps) env (cdr parameters))))
        (else
         (cons (xeval (first-operand exps) env)
               (special-values (rest-operands exps) env (cdr parameters))))))

;;remove special argument tags
(define (execution-parameters parameters)
  (cond ((null? parameters) '())
        ((pair? (car parameters))
         (cons (cadr (car parameters)) (execution-parameters (cdr parameters))))
        (else
         (cons (car parameters) (execution-parameters (cdr parameters))))))

;;sepcial evaluation rules for special arguments
(define (special-argument parameter)
    (cond ((tagged-list? parameter 'delayed) delayed-eval)
          ((tagged-list? parameter 'dynamic) dynamic-eval)
          (else reference-eval)))

;;delayed
(define (delayed? obj)
  (tagged-list? obj '<thunk>))

(define (delayed-eval exp env)
  (list '<thunk> exp (lambda () env)))

;;dynamic
(define the-dynamic-environment '())

(define (pop-dynamic)
  (set! the-dynamic-environment
        (enclosing-environment the-dynamic-environment)))

(define (push-dynamic frame)
  (set! the-dynamic-environment
        (cons frame the-dynamic-environment)))

(define (dynamic-eval exp env)
  (xeval exp the-dynamic-environment))

;;reference
(define (reference? obj)
  (tagged-list? obj 'reference))

(define (reference-eval exp env)
  (if (defined-variable? exp env)
      (list 'reference exp env)
      (s450error "Defined symbol required for reference formal argument")))

;;; Special forms

(define (isolated-special-form? exp)
  (lookup-action exp))

(define special-forms
  (list '*table*))

(define (type-of exp)
  (if (pair? exp)
      (car exp)
      #f))

(define (lookup-action type)
  (define (lookup key table)
    (let ((record (assoc key (cdr table))))
      (if record
          (cdr record)
          #f)))
  (lookup type special-forms))

;; when a variable has been assigned a special form
(define (lookup-as-variable var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (car vals))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        #f
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (lookup-action (env-loop env)))

(define (install-special-form name proc)
  (define (insert! key value table)
    (let ((record (assoc key (cdr table))))
      (if record
          (set-cdr! record value)
          (set-cdr! table
                    (cons (cons key value) (cdr table))))))
  (cond ((lookup-action name) (error "Special form already defined"))
        ((defined-variable? name the-global-environment)
         (error "Already defined as a variable"))
        (else (insert! name proc special-forms)))
  name)

;;; New special forms

(define (variable exp)
  (cadr exp))

(define (locally-unbound! name env)
  (define (var-iter vars);;remove var
    (cond ((null? vars) '())
          ((equal? name (car vars))
           (cdr vars))
          (else
           (cons (car vars) (var-iter (cdr vars))))))
  (define (val-iter vars vals);;remove val
    (cond ((null? vals) '())
          ((equal? name (car vars))
           (cdr vals))
          (else
           (cons (car vals) (val-iter (cdr vars) (cdr vals))))))
  (let ((frame (first-frame env)))
    (set-cdr! frame (val-iter (frame-variables frame)
                              (frame-values frame)))
    (set-car! frame (var-iter (frame-variables frame))))
  'ok)

(define (unbound! name env)
  (if (equal? env the-empty-environment)
      'ok
      (begin (locally-unbound! name env)
             (unbound! name (enclosing-environment env)))))

(define (locally-defined-variable? name env)
  (define (scan-vars vars)
    (cond ((null? vars)
           #f)
          ((equal? name (car vars))
           #t)
          (else (scan-vars (cdr vars)))))
  (let ((frame (first-frame env)))
    (scan-vars (frame-variables frame))))

(define (defined-variable? name env)
  (cond ((equal? env the-empty-environment)
         #f)
        ((locally-defined-variable? name env)
         #t)
        (else
         (defined-variable? name (enclosing-environment env)))))

;;; primitive procedure (exit) and (s450error args)

(define restart '())

(define (exit)
  (restart #f))

(define (s450error . args)
  (newline)
  (display "Error: ")
  (apply display* args)
  (newline)
  (newline)
  (display "Reset. (Use Control-d or (exit) to quit s450)")
  (restart #t))

;;; Handling procedure arguments

(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (cons (xeval (first-operand exps) env)
            (list-of-values (rest-operands exps) env))))

;;; These functions, called from xeval, do the work of evaluating some
;;; of the special forms:

(define (eval-if exp env)
  (if (true? (xeval (if-predicate exp) env))
      (xeval (if-consequent exp) env)
      (xeval (if-alternative exp) env)))

(define (eval-sequence exps env)
  (cond ((last-exp? exps) (xeval (first-exp exps) env))
        (else (xeval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (eval-assignment exp env)
  (let ((name (assignment-variable exp)))
    (if (lookup-action name)
        (s450error "Cannot assign to a special form name")
        (set-variable-value! name
                             (xeval (assignment-value exp) env)
                             env))
    name))    ;; A & S return 'ok

(define (eval-definition exp env)
  (let ((name (definition-variable exp)))
    (if (lookup-action name)
        (s450error "Cannot redefine a special form")
        (define-variable! name
          (xeval (definition-value exp) env)
          env))
    name))     ;; A & S return 'ok

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Representing expressions
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Numbers, strings, and booleans are all represented as themselves.
;;; (Not characters though; they don't seem to work out as well
;;; because of an interaction with read and display.)

(define (self-evaluating? exp)
  (or (number? exp)
      (string? exp)
      (boolean? exp)
      ))

;;; variables -- represented as symbols

(define (variable? exp) (symbol? exp))

;;; quote -- represented as (quote <text-of-quotation>)

(define (quoted? exp)
  (tagged-list? exp 'quote))

(define (text-of-quotation exp) (cadr exp))

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))

;;; assignment -- represented as (set! <var> <value>)

(define (assignment? exp) 
  (tagged-list? exp 'set!))

(define (assignment-variable exp) (cadr exp))

(define (assignment-value exp) (caddr exp))

;;; definitions -- represented as
;;;    (define <var> <value>)
;;;  or
;;;    (define (<var> <parameter_1> <parameter_2> ... <parameter_n>) <body>)
;;;
;;; The second form is immediately turned into the equivalent lambda
;;; expression.

(define (definition? exp)
  (tagged-list? exp 'define))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (cddr exp))))

;;; lambda expressions -- represented as (lambda ...)
;;;
;;; That is, any list starting with lambda.  The list must have at
;;; least one other element, or an error will be generated.

(define (lambda? exp) (tagged-list? exp 'lambda))

(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

;;; conditionals -- (if <predicate> <consequent> <alternative>?)

(define (if? exp) (tagged-list? exp 'if))

(define (if-predicate exp) (cadr exp))

(define (if-consequent exp) (caddr exp))

(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      #f))

(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))


;;; sequences -- (begin <list of expressions>)

(define (begin? exp) (tagged-list? exp 'begin))

(define (begin-actions exp) (cdr exp))

(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq) (cons 'begin seq))


;;; procedure applications -- any compound expression that is not one
;;; of the above expression types.

(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))

(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))


;;; Derived expressions -- the only one we include initially is cond,
;;; which is a special form that is syntactically transformed into a
;;; nest of if expressions.

(define (cond? exp) (tagged-list? exp 'cond))

(define (cond-clauses exp) (cdr exp))

(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))

(define (cond-predicate clause) (car clause))

(define (cond-actions clause) (cdr clause))

(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (if (null? clauses)
      #f                          ; no else clause -- return #f
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp (cond-actions first))
                (s450error "ELSE clause isn't last -- COND->IF "
                       clauses))
            (make-if (cond-predicate first)
                     (sequence->exp (cond-actions first))
                     (expand-clauses rest))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Truth values and procedure objects
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Truth values

(define (true? x)
  (not (eq? x #f)))

(define (false? x)
  (eq? x #f))


;;; Procedures

(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

(define (user-defined-procedure? p)
  (tagged-list? p 'procedure))

(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Representing environments
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; An environment is a list of frames.

(define (enclosing-environment env) (cdr env))

(define (first-frame env) (car env))

(define the-empty-environment '())

;;; Each frame is represented as a pair of lists:
;;;   1.  a list of the variables bound in that frame, and
;;;   2.  a list of the associated values.

(define (make-frame variables values)
  (cons variables values))

(define (frame-variables frame) (car frame))
(define (frame-values frame) (cdr frame))

(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (cons val (cdr frame))))

;;; Extending an environment

(define (xtend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (let ((frame (make-frame vars vals)))
        (begin (push-dynamic frame)
               (cons frame base-env)))
      (if (< (length vars) (length vals))
          (s450error "Too many arguments supplied " vars vals)
          (s450error "Too few arguments supplied " vars vals))))

;;; Looking up a variable in an environment

(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (car vals))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (s450error "Unbound variable " var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

;;; Setting a variable to a new value in a specified environment.
;;; Note that it is an error if the variable is not already present
;;; (i.e., previously defined) in that environment.

(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (s450error "Unbound variable -- SET! " var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (let ((value (lookup-variable-value var env)))
    (if (reference? value)
        (set-variable-value! (saved-exp value) val (saved-env value))
        (env-loop env))))

;;; Defining a (possibly new) variable.  First see if the variable
;;; already exists.  If it does, just change its value to the new
;;; value.  If it does not, define the new variable in the current
;;; frame.

(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (cond ((null? vars)
             (add-binding-to-frame! var val frame))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (scan (frame-variables frame)
          (frame-values frame))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 The initial environment
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This is initialization code that is executed once, when the the
;;; interpreter is invoked.

(define (setup-environment)
  (let ((initial-env
         (xtend-environment '()
                            '()
                            the-empty-environment)))
    initial-env))

;;; Define the primitive procedures

(define (install-primitive-procedure name action)
  (if (lookup-action name)
      (error "Already defined as a special form")
      (add-binding-to-frame! name
                            (list 'primitive action)
                            (first-frame the-global-environment)))
  name)

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define (primitive-implementation proc) (cadr proc))

;;; Here is where we rely on the underlying Scheme implementation to
;;; know how to apply a primitive procedure.

(define (apply-primitive-procedure proc args)
  (apply (primitive-implementation proc) args))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 The main driver loop
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Note that (read) returns an internal representation of the next
;;; Scheme expression from the input stream.  It does NOT evaluate
;;; what is typed in -- it just parses it and returns an internal
;;; representation.  It is the job of the scheme evaluator to perform
;;; the evaluation.  In this case, our evaluator is called xeval.

(define input-prompt "s450==> ")

;; Wrapper function for the original s450 procedure, now named s450-loop
(define (s450)
  (if (s450-loop)
      (s450)
      (begin (newline)
             (display "Exiting s450..."))))

(define (s450-loop)
  (call/cc
   (lambda (return)
     (set! restart return)
     (prompt-for-input input-prompt)
     (let ((input (read)))
       (let ((output (xeval input the-global-environment)))
             (user-print output)))
     (s450-loop))))

(define (prompt-for-input string)
  (newline) (newline) (display string))

;;; Note that we would not want to try to print a representation of the
;;; <procedure-env> below -- this would in general get us into an
;;; infinite loop.

(define (user-print object)
  (if (user-defined-procedure? object)
      (display (list 'user-defined-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (if (isolated-special-form? object)
          (begin (display "Special form: ")
                 (display object))
          (display object))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;	 Here we go:  define the global environment and invite the
;;;        user to run the evaluator.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define the-global-environment (setup-environment))

(install-primitive-procedure 'car car)

(install-primitive-procedure 'cdr cdr)

(install-primitive-procedure 'cons cons)

(install-primitive-procedure 'null null?)

(install-primitive-procedure '+ +)

(install-primitive-procedure 'display display)

(install-primitive-procedure 'newline newline)

(install-primitive-procedure 'exit exit)

;; Stream operations

(define (s450-stream-cdr strm)
  (xeval (cdr strm) '()))

(install-primitive-procedure 'stream-car car)

(install-primitive-procedure 'stream-cdr s450-stream-cdr)

(install-primitive-procedure 'stream-null? null?)

(install-special-form
 'cons-stream (lambda (exp env) (cons (xeval (cadr exp) env)
                                      (delayed-eval (caddr exp) env))))

(add-binding-to-frame! 'the-empty-environment '()
                       (first-frame the-global-environment))

;;; Install special forms

(install-special-form
 'quote (lambda (exp env)
          (text-of-quotation exp)))

(install-special-form
 'set! (lambda (exp env)
         (eval-assignment exp env)))

(install-special-form
 'define (lambda (exp env)
           (eval-definition exp env)))

(install-special-form
 'if (lambda (exp env)
       (eval-if exp env)))

(install-special-form
 'lambda (lambda (exp env)
           (make-procedure (lambda-parameters exp)
                           (lambda-body exp)
                           env)))

(install-special-form
 'begin (lambda (exp env)
          (eval-sequence (begin-actions exp) env)))

(install-special-form
 'cond (lambda (exp env)
         (xeval (cond->if exp) env)))

(install-special-form
 'defined? (lambda (exp env)
             (defined-variable? (variable exp) env)))

(install-special-form
 'locally-defined? (lambda (exp env)
                     (locally-defined-variable? (variable exp) env)))

(install-special-form
 'make-unbound! (lambda (exp env)
                  (unbound! (variable exp) env)))

(install-special-form
 'locally-make-unbound! (lambda (exp env)
                          (locally-unbound! (variable exp) env)))

(display "... loaded the metacircular evaluator. (s450) runs it.")
(newline)
