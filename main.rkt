; If you are using scheme instead of racket, comment these two lines, uncomment the (load "simpleParser.scm") and comment the (require "simpleParser.rkt")
#lang racket
(require "classParser.rkt")
;(require "functionParser.rkt")
; (load "simpleParser.scm")

; An interpreter for the simple language using tail recursion for the M_state functions.

; The functions that start interpret-...  all return the current environment.  These are the M_state functions.
; The functions that start eval-...  all return a value.  These are the M_value and M_boolean functions.

; The main function.  Calls parser to get the parse tree and interprets it with a new environment.  Sets default continuations for return, break, continue, throw, and "next statement"
; This is a modified main function to work with the 'two passes' structure
;Created by Group 13 - Sasha Wallace, Joanna Elia, and Ryan Saathoff
(define interpret
  (lambda (mainclass file)
    (scheme->language
     (interpret-class-list mainclass (class-definitions-list (parser file) (newclassstate) (lambda (cs) cs))))))

; runs a first pass to declare classes with fields and methods
; cs stands for class state, the output of the first pass
(define interpret-class-list
  (lambda (mainclass cs)
    (interpret-statement-list (get-function-statements 'main (get-class-state mainclass cs)) (push-frame (remove 'main (function-state 'main (get-class-state mainclass cs))))
                                (lambda (v env) v) (lambda (env) (myerror "Break used outside of loop")) (lambda (env) (myerror "Continue used outside of loop"))
                                (lambda (v env) (myerror "Uncaught exception thrown")) (lambda (env) env) cs mainclass)))

; these help run through lists of classes
(define class-definitions-list
  (lambda (statements classstate next)
    (if (null? statements)
        (next classstate)
        (interpret-class (car statements) classstate (lambda (cs) (class-definitions-list (cdr statements) cs next))))))

(define interpret-class
  (lambda (statements classstate next)
    (if (eq? (car statements) 'class)
        (next (insert-class (cadr statements) (cons (caddr statements)
                       (function-definitions-list (cadddr statements) (newenvironment) (lambda (env) env) (cadr statements))) classstate))
        (myerror "Unkown statement:" (car statements)))))


; Runs a 'first pass' of the class to declare variables and function definitions
; cc tracks the current class
(define function-definitions-list
  (lambda (statements environment next cc)
    (if (null? statements)
        (next environment)
        (function-definitions (car statements) environment (lambda (env) (function-definitions-list (cdr statements) env next cc)) cc))))

; Interprets each part in the initial pass. For now, static functions are treated the same as non-static
(define function-definitions
  (lambda (statement environment next cc)
    (cond
      ((eq? 'static-function (statement-type statement)) (interpret-function statement environment next cc))
      ((eq? 'function (statement-type statement)) (interpret-function statement environment next cc))
      ((eq? 'var (statement-type statement)) (define-declare statement environment next))
      (else (myerror "Unknown statement:" (statement-type statement)))
      )))

; Store the function definition: stored like a variable with the value being a list containing the parameter list and function-statement lists
(define interpret-function
  (lambda (statement environment next cc)
    (next (insert-function (get-declare-var statement) (cons cc (function-body statement)) environment))))

; interprets a list of statements.  The state/environment from each statement is used for the next ones.
(define interpret-statement-list
  (lambda (statement-list environment return break continue throw next cs cc)
    (if (null? statement-list)
        (next environment)
        (interpret-statement (car statement-list) environment return break continue throw (lambda (env) (interpret-statement-list (cdr statement-list) env return break continue throw next cs cc)) cs cc))))

; interpret a statement in the environment with continuations for return, break, continue, throw, and "next statement"
(define interpret-statement
  (lambda (statement environment return break continue throw next cs cc)
    (cond
      ((eq? 'return (statement-type statement)) (interpret-return statement environment return break continue throw next cs cc))
      ((eq? 'var (statement-type statement)) (interpret-declare statement environment return break continue throw next cs cc))
      ((eq? '= (statement-type statement)) (interpret-assign statement environment return break continue throw next cs cc))
      ((eq? 'if (statement-type statement)) (interpret-if statement environment return break continue throw next cs cc))
      ((eq? 'while (statement-type statement)) (interpret-while statement environment return break continue throw next cs cc))
      ((eq? 'continue (statement-type statement)) (continue environment))
      ((eq? 'break (statement-type statement)) (break environment))
      ((eq? 'begin (statement-type statement)) (interpret-block statement environment return break continue throw next cs cc))
      ((eq? 'throw (statement-type statement)) (interpret-throw statement environment return break continue throw next cs cc))
      ((eq? 'try (statement-type statement)) (interpret-try statement environment return break continue throw next cs cc))
      ((eq? 'function (statement-type statement)) (interpret-function statement environment next cc))
      ((eq? 'funcall (statement-type statement)) (run-function statement environment (lambda (v env) (next env)) break continue (lambda (v env) (throw v environment)) next cs cc))
      (else (myerror "Unknown statement:" (statement-type statement))))))

;evaluates function calls - maybe use old version for static functions?
;(define run-function
  ;(lambda (statement environment return break continue throw next cs)
   ; (interpret-statement-list (get-function-statements (fname statement) environment)
                     ;(bind-parameters (get-parameters (fname statement) environment) (params-body statement) (push-frame (function-state (fname statement) environment)) return break continue throw next environment)
                   ;  return
                  ;   (lambda (env) (break environment))
                    ;                     (lambda (env) (continue environment))
                    ;                     (lambda (v env) (throw v environment))
                    ;                     (lambda (env) (next environment)) cs)))

; runs a function from the function closure
(define run-function
  (lambda (statement environment return break continue throw next cs cc)
    (let ((closure (eval-expression (cadr statement) environment return break continue throw next cs cc)))
      (if (list? (cadr statement))
          (interpret-statement-list (caddr closure)
                                    (bind-parameters (cadr closure) (cddr statement)
                                                     (push-frame (get-instance-env (eval-expression (assign-class statement) environment return break continue throw next cs cc) environment)) return break continue throw next environment cs cc)
                                    return
                                    (lambda (env) (break environment)) (lambda (env) (continue environment))
                                    (lambda (v env) (throw v environment)) (lambda (env) (next environment)) cs (currentclass (eval-expression (assign-class statement) environment return break continue throw next cs cc)))
          (interpret-statement-list (caddr closure)
                                    (bind-parameters (cadr closure) (cddr statement)
                                                     (push-frame (function-state (cadr statement)
                                                                                 environment)) return break continue throw next environment cs cc)
                                    return
                                    (lambda (env) (break environment)) (lambda (env) (continue environment))
                                    (lambda (v env) (throw v environment)) (lambda (env) (next environment)) cs (car closure))
          ))))

; Adds a new variable binding to the environment.  There may be an assignment with the variable
(define define-declare
  (lambda (statement environment next)
    (if (exists-declare-value? statement)
        (next (insert (get-declare-var statement) (get-declare-value statement) environment))
        (next (insert (get-declare-var statement) 'novalue environment)))))

; Calls the return continuation with the given expression value
(define interpret-return
  (lambda (statement environment return break continue throw next cs cc)
    (return (eval-expression (get-expr statement) environment return break continue throw next cs cc) environment)))

; Adds a new variable binding to the environment.  There may be an assignment with the variable
(define interpret-declare
  (lambda (statement environment return break continue throw next cs cc)
    (if (exists-declare-value? statement)
        (next (insert (get-declare-var statement) (eval-expression (get-declare-value statement) environment return break continue throw next cs cc) environment))
        (next (insert (get-declare-var statement) 'novalue environment)))))

; Updates the environment to add a new binding for a variable
(define interpret-assign
  (lambda (statement environment return break continue throw next cs cc)
    (if (list? (get-assign-lhs statement))
        (next (update (assign-class statement) (redefine-instance
                                                (update (assign-class-var statement)
                                                        (eval-expression (get-assign-rhs statement) environment return break continue throw next cs cc)
                                                        (get-instance-env (lookup (assign-class statement) environment) environment))
                                                (lookup (assign-class statement) environment))
                      environment))
        (next (update (get-assign-lhs statement) (eval-expression (get-assign-rhs statement) environment return break continue throw next cs cc) environment)))))

; We need to check if there is an else condition.  Otherwise, we evaluate the expression and do the right thing.
(define interpret-if
  (lambda (statement environment return break continue throw next cs cc)
    (cond
      ((eval-expression (get-condition statement) environment return break continue throw next cs cc) (interpret-statement (get-then statement) environment return break continue throw next cs cc))
      ((exists-else? statement) (interpret-statement (get-else statement) environment return break continue throw next cs cc))
      (else (next environment)))))

; Interprets a while loop.  We must create break and continue continuations for this loop
(define interpret-while
  (lambda (statement environment return break continue throw next cs cc)
    (letrec ((loop (lambda (condition body environment)
                     (if (eval-expression condition environment return break continue throw next cs cc)
                         (interpret-statement body environment return (lambda (env) (next env)) (lambda (env) (loop condition body env)) throw (lambda (env) (loop condition body env)) cs cc)
                         (next environment)))))
      (loop (get-condition statement) (get-body statement) environment))))

; Interprets a block.  The break, continue, throw and "next statement" continuations must be adjusted to pop the environment
(define interpret-block
  (lambda (statement environment return break continue throw next cs cc)
    (interpret-statement-list (cdr statement)
                                         (push-frame environment)
                                         return
                                         (lambda (env) (break (pop-frame env)))
                                         (lambda (env) (continue (pop-frame env)))
                                         (lambda (v env) (throw v (pop-frame env)))
                                         (lambda (env) (next (pop-frame env))) cs cc)))

; We use a continuation to throw the proper value
(define interpret-throw
  (lambda (statement environment return break continue throw next cs cc)
    (throw (eval-expression (get-expr statement) environment return break continue throw next cs cc) environment)))

; Interpret a try-catch-finally block

; Create a continuation for the throw.  If there is no catch, it has to interpret the finally block, and once that completes throw the exception.
; Otherwise, it interprets the catch block with the exception bound to the thrown value and interprets the finally block when the catch is done
(define create-throw-catch-continuation
  (lambda (catch-statement environment return break continue throw next finally-block cs cc)
    (cond
      ((null? catch-statement) (lambda (ex env) (interpret-block finally-block env return break continue throw (lambda (env2) (throw ex env2)) cs cc))) 
      ((not (eq? 'catch (statement-type catch-statement))) (myerror "Incorrect catch statement"))
      (else (lambda (ex env)
                  (interpret-statement-list 
                       (get-body catch-statement) 
                       (insert (catch-var catch-statement) ex (push-frame env))
                       return 
                       (lambda (env2) (break (pop-frame env2))) 
                       (lambda (env2) (continue (pop-frame env2))) 
                       (lambda (v env2) (throw v (pop-frame env2))) 
                       (lambda (env2) (interpret-block finally-block (pop-frame env2) return break continue throw next cs cc)) cs cc))))))

; To interpret a try block, we must adjust  the return, break, continue continuations to interpret the finally block if any of them are used.
; We must create a new throw continuation and then interpret the try block with the new continuations followed by the finally block with the old continuations
(define interpret-try
  (lambda (statement environment return break continue throw next cs cc)
    (let* ((finally-block (make-finally-block (get-finally statement)))
           (try-block (make-try-block (get-try statement)))
           (new-return (lambda (v env) (interpret-block finally-block environment return break continue throw (lambda (env2) (return v)) cs cc)))
           (new-break (lambda (env) (interpret-block finally-block env return break continue throw (lambda (env2) (break env2)) cs cc)))
           (new-continue (lambda (env) (interpret-block finally-block env return break continue throw (lambda (env2) (continue env2)) cs cc)))
           (new-throw (create-throw-catch-continuation (get-catch statement) environment return break continue throw next finally-block cs cc)))
      (interpret-block try-block environment new-return new-break new-continue new-throw (lambda (env) (interpret-block finally-block env return break continue throw next cs cc)) cs cc))))

; helper methods so that we can reuse the interpret-block method on the try and finally blocks
(define make-try-block
  (lambda (try-statement)
    (cons 'begin try-statement)))

(define make-finally-block
  (lambda (finally-statement)
    (cond
      ((null? finally-statement) '(begin))
      ((not (eq? (statement-type finally-statement) 'finally)) (myerror "Incorrectly formatted finally block"))
      (else (cons 'begin (cadr finally-statement))))))

; Evaluate an expression using eval-expression-cps
(define eval-expression
  (lambda (expr environment return break continue throw next cs cc)
    (eval-expression-cps expr environment return break continue throw next (lambda (v) v) cs cc)))

; Evaluates all possible boolean and arithmetic expressions, including constants and variables.
(define eval-expression-cps
  (lambda (expr environment return break continue throw next eval-return cs cc)
    (cond
      ((number? expr) (eval-return expr))
      ((eq? expr 'true) (eval-return #t))
      ((eq? expr 'false) (eval-return #f))
      ((not (list? expr)) (eval-return (lookup expr environment)))
      ((eq? (operator expr) 'funcall) (eval-return (run-function expr environment (lambda (v env) v) break continue throw next cs cc)))
      ((eq? (operator expr) 'new) (eval-return (create-class-instance (operand1 expr) cs)))
      ((eq? (operator expr) 'dot) (eval-return (dot-op (cadr expr) (caddr expr) environment return break continue throw next cs cc)))
      (else (eval-operator expr environment return break continue throw next eval-return cs cc)))))

;helper function for evaluating dot
(define dot-op
  (lambda (class var enviroment return break continue throw next cs cc)
    (cond
      ((eq? class 'this) (lookup var (super-env cc enviroment (lambda (env) env))))
      ((eq? class 'super) (lookup var (super-env cc enviroment (lambda (env) (pop-frame env)))))
      (else  (lookup var (get-instance-env (eval-expression class enviroment return break continue throw next cs cc) enviroment))))))

; Evaluate a binary (or unary) operator
(define eval-operator
  (lambda (expr environment return break continue throw next eval-return cs cc)
    (cond
      ((eq? '! (operator expr)) (eval-expression-cps (operand1 expr) environment return break continue throw next (lambda (v) (eval-return (not v))) cs cc))
      ((and (eq? '- (operator expr)) (= 2 (length expr))) (eval-expression-cps (operand1 expr) environment return break continue throw next (lambda (v) (eval-return (- v))) cs cc))
      (else (eval-expression-cps (operand1 expr) environment return break continue throw next (lambda (v) (eval-binary-op2 expr v  environment return break continue throw next eval-return cs cc)) cs cc)))))

; Complete the evaluation of the binary operator by evaluating the second operand and performing the operation
(define eval-binary-op2
  (lambda (expr op1value environment return break continue throw next eval-return cs cc)
    (cond
      ((eq? '+ (operator expr)) (eval-expression-cps (operand2 expr) environment return break continue throw next (lambda (v) (eval-return (+ op1value v))) cs cc))
      ((eq? '- (operator expr)) (eval-expression-cps (operand2 expr) environment return break continue throw next (lambda (v) (eval-return (- op1value v))) cs cc))
      ((eq? '* (operator expr)) (eval-expression-cps (operand2 expr) environment return break continue throw next (lambda (v) (eval-return (* op1value v))) cs cc))
      ((eq? '/ (operator expr)) (eval-expression-cps (operand2 expr) environment return break continue throw next (lambda (v) (eval-return (quotient op1value v))) cs cc))
      ((eq? '% (operator expr)) (eval-expression-cps (operand2 expr) environment return break continue throw next (lambda (v) (eval-return (remainder op1value v))) cs cc))
      ((eq? '== (operator expr)) (eval-expression-cps (operand2 expr) environment return break continue throw next (lambda (v) (eval-return (isequal op1value v))) cs cc))
      ((eq? '!= (operator expr)) (eval-expression-cps (operand2 expr) environment return break continue throw next (lambda (v) (eval-return (not (isequal op1value v)))) cs cc))
      ((eq? '< (operator expr)) (eval-expression-cps (operand2 expr) environment return break continue throw next (lambda (v) (eval-return (< op1value v))) cs cc))
      ((eq? '> (operator expr)) (eval-expression-cps (operand2 expr) environment return break continue throw next (lambda (v) (eval-return (> op1value v))) cs cc))
      ((eq? '<= (operator expr)) (eval-expression-cps (operand2 expr) environment return break continue throw next (lambda (v) (eval-return (<= op1value v))) cs cc))
      ((eq? '>= (operator expr))  (eval-expression-cps (operand2 expr) environment return break continue throw next (lambda (v) (eval-return (>= op1value v))) cs cc))
      ((eq? '|| (operator expr)) (eval-expression-cps (operand2 expr) environment return break continue throw next (lambda (v) (eval-return (or op1value v))) cs cc))
      ((eq? '&& (operator expr)) (eval-expression-cps (operand2 expr) environment return break continue throw next (lambda (v) (eval-return (and op1value v))) cs cc))
      (else (myerror "Unknown operator:" (operator expr))))))

; Determines if two values are equal.  We need a special test because there are both boolean and integer types.
(define isequal
  (lambda (val1 val2)
    (if (and (number? val1) (number? val2))
        (= val1 val2)
        (eq? val1 val2))))

;------------------------
; Environment/State Functions
;------------------------

; instance functions
(define redefine-instance
  (lambda (newclose oldclose)
    (if (not (list? oldclose))
        newclose
        (list (car oldclose) newclose))))

(define get-instance-env
  (lambda (cclosure environment)
    (cond
      ((not (list? cclosure)) (function-state 'this environment))
      (else (cadr cclosure)))))

; finding the super class definitions
(define super-env
  (lambda (cc env f)
    (cond
      ((null? env) (myerror "error: can't find super:" cc))
      ((and (exists-in-list? 'this (variables (topframe env))) (eq? cc (lookup-in-frame 'this (variables (topframe env)) (store (topframe env))))) (f env))
      ((and (exists-in-list? 'super (variables (topframe env))) (eq? cc (lookup-in-frame 'super (variables (topframe env)) (store (topframe env))))) (f env))
      (else (super-env cc (cdr env) f)))))

;for creating a new instance of a class
(define create-class-instance
  (lambda (cname cs)
    (list cname (remove 'main (new-instance-boxes* (get-class-state cname cs))))))

; when a new instance of a class is creating, we make new boxes so that fields don't collide
(define new-instance-boxes*
  (lambda (lis)
    (cond
      ((null? lis) '())
      ((list? (car lis)) (cons (new-instance-boxes* (car lis)) (new-instance-boxes* (cdr lis))))
      ((box? (car lis)) (cons (box (unbox (car lis))) (new-instance-boxes* (cdr lis))))
      (else (cons (car lis) (new-instance-boxes* (cdr lis))))))) 

;returns the class state for a particular class from the class state
;old for reference
(define get-class-state1
  (lambda (cname cs)
    (let ((close (get-class-closure cname cs)))
      (if (null? (super-class close))
          (insert 'this 'this (closure-body close))
          (insert 'super (create-class-instance (extended-class close) cs) (insert 'this 'this (closure-body close)))))))

;new
(define get-class-state
  (lambda (cname cs)
    (get-cs 'this cname cs)))
 (define get-cs
  (lambda (poly cname cs)
    (let ((close (get-class-closure cname cs)))
      (if (null? (super-class close))
          (insert poly cname (closure-body close))
          (cons (car (insert poly cname (closure-body close))) (get-cs 'super (extended-class close) cs))))))

; class-state functions
(define newclassstate
  (lambda ()
    '(() ())))

; for defining a class
(define insert-class
  (lambda (cname cclose cs)
    (list (cons cname (variables cs)) (cons (box cclose) (store cs)))))

; returns the class closure for a particular class from the class state
(define get-class-closure
  (lambda (cname cs)
    (cond
      ((not (exists-in-list? cname (variables cs))) (myerror "error: undefined class" cname))
      ((eq? cname (car (variables cs))) (firstvalue (store cs)))
      (else (get-class-closure cname (cdrlayer cs))))))

; gets parameters from closure
(define get-parameters
  (lambda (fname environment)
    (cadr (get-closure fname environment))))

;get state for function
(define function-state
  (lambda (fname environment)
    (cond
      ((null? environment) (myerror "error: undefined function" fname))
      ((exists-in-list? fname (fnamelist (topframe environment))) environment)
      (else (function-state fname (pop-frame environment))))))

; get statement list that a function runs
(define get-function-statements
  (lambda (fname environment)
    (caddr (get-closure fname environment))))

; takes list of parameters and list of arguments or expressions and adds them to the given environment (create new layer in call)
(define bind-parameters
  (lambda (fparam fargs newenv return break continue throw next oldenv cs cc)
    (cond
      ((and (null? fparam) (null? fargs)) newenv)
      ((null? fparam) (myerror "error: too many argumetents" 'null))
      ((null? fargs) (myerror "error: missing value for parameter" (car fparam)))
      (else (bind-parameters (cdr fparam) (cdr fargs) (insert (car fparam) (eval-expression (car fargs) oldenv return break continue throw next cs cc) newenv)
                             return break continue throw next oldenv cs cc)))))

; creates closure of a function
(define create-closure
  (lambda (environment param-statements)
    (cons environment param-statements)))

; gets closure of a function
(define get-closure
  (lambda (fname environment)
    (lookup-variable fname environment)))

; create a new empty environment
(define newenvironment
  (lambda ()
    (list (newframe))))

; create an empty frame: a frame is two lists, the first are the variables and the second is the "store" of values
(define newframe
  (lambda ()
    '(() ())))
       
; add a frame onto the top of the environment
(define push-frame
  (lambda (environment)
    (cons (newframe) environment)))

; remove a frame from the environment
(define pop-frame
  (lambda (environment)
    (cdr environment)))

; does a variable exist in the environment?
(define exists?
  (lambda (var environment isvar)
    (cond
      ((null? environment) #f)
      ((exists-in-list? var (variables (topframe environment))) #t)
      (else (exists? var (remainingframes environment) isvar)))))

; does a variable exist in a list?
(define exists-in-list?
  (lambda (var varlist)
    (cond
      ((null? varlist) #f )
      ((eq? var (car varlist))  #t)
      (else (exists-in-list? var (cdr varlist))))))

; Looks up a value in the environment.  If the value is a boolean, it converts our languages boolean type to a Scheme boolean type
(define lookup
  (lambda (var environment)
    (lookup-variable var environment)))
  
; A helper function that does the lookup.  Returns an error if the variable does not have a legal value
(define lookup-variable
  (lambda (var environment)
    (let ((value (lookup-in-env var environment)))
      (if (eq? 'novalue value)
          (myerror "error: variable without an assigned value:" var)
          value))))

; Return the value bound to a variable in the environment
(define lookup-in-env
  (lambda (var environment)
    (cond
      ((null? environment) (myerror "error: undefined in environment" var))
      ((exists-in-list? var (variables (topframe environment))) (lookup-in-frame var (variables (topframe environment)) (store (topframe environment))))
      (else (lookup-in-env var (cdr environment))))))

;Finds a variable in the current frame
(define lookup-in-frame
  (lambda (var varlist vallist)
    (cond
      ((null? varlist) (myerror "error: undefined" var))
      ((eq? var (car varlist)) (language->scheme (firstvalue vallist)))
      (else     (lookup-in-frame var (cdr varlist) (cdr vallist))))))

;Remove something from the current environment
(define remove
  (lambda (var env)
    (cons (remove-in-frame var (variables (topframe env)) (store (topframe env)) (lambda (l1 l2) (list l1 l2))) (cdr env))))

(define remove-in-frame
  (lambda (var varlist vallist return)
    (cond
      ((null? varlist) (return '() '()))
      ((eq? var (car varlist)) (return (cdr varlist) (cdr vallist)))
      (else (remove-in-frame var (cdr varlist) (cdr vallist) (lambda (l1 l2) (return (cons (car varlist) l1) (cons (car vallist) l2))))))))

;These are for defining and declaring functions
(define insert-function
  (lambda (fname fclosure environment)
    (cons (add-to-frame-function fname fclosure (car environment)) (cdr environment))
     ))

(define add-to-frame-function
  (lambda (fname fclosure frame)
    (list (cons fname (fnamelist frame)) (cons (box (scheme->language fclosure)) (fcloselist frame)))))

; Adds a new variable/value binding pair into the environment.  Gives an error if the variable already exists in this frame.
(define insert
  (lambda (var val environment)
    (if (exists-in-list? var (variables (topframe environment)))
        (myerror "error: variable is being re-declared:" var)
        (cons (add-to-frame var val (car environment)) (cdr environment)))))

; Changes the binding of a variable to a new value in the environment.  Gives an error if the variable does not exist.
(define update
  (lambda (var val environment)
    (cond
      ((eq? var 'this) val)
      ((exists? var environment #t) (update-existing var val environment))
      (else (myerror "error: variable used but not defined:" var)))))

; Add a new variable/value pair to the frame.
(define add-to-frame
  (lambda (var val frame)
    (list (cons var (variables frame)) (cons (box (scheme->language val)) (store frame)))))

; Changes the binding of a variable in the environment to a new value
(define update-existing
  (lambda (var val environment)
    (if (exists-in-list? var (variables (topframe environment)))
        (cons (update-in-frame var val (topframe environment)) (remainingframes environment))
        (cons (topframe environment) (update-existing var val (remainingframes environment))))))

; Changes the binding of a variable in the frame to a new value.
(define update-in-frame
  (lambda (var val frame)
    (list (variables frame) (update-in-frame-store var val (variables frame) (store frame)))))

; Changes a variable binding by placing the new value in the appropriate place in the store
(define update-in-frame-store
  (lambda (var val varlist vallist)
    (cond
      ((eq? var (car varlist)) (begin (set-box! (car vallist) val) vallist))
      (else (cons (car vallist) (update-in-frame-store var val (cdr varlist) (cdr vallist)))))))

; Functions to convert the Scheme #t and #f to our languages true and false, and back.
(define language->scheme
  (lambda (v) 
    (cond 
      ((eq? v 'false) #f)
      ((eq? v 'true) #t)
      (else v))))

(define scheme->language
  (lambda (v)
    (cond
      ((eq? v #f) 'false)
      ((eq? v #t) 'true)
      (else v))))

; Because the error function is not defined in R5RS scheme, we create our own:
(define error-break (lambda (v) v))
(call-with-current-continuation (lambda (k) (set! error-break k)))
(define myerror
  (lambda (str . vals)
    (letrec ((makestr (lambda (str vals)
                        (if (null? vals)
                            str
                            (makestr (string-append str (string-append " " (symbol->string (car vals)))) (cdr vals))))))
      (error-break (display (string-append str (makestr "" vals)))))))


;-----------------
; HELPER FUNCTIONS
;-----------------

; These helper functions define the operator and operands of a value expression
(define operator car)
(define operand1 cadr)
(define operand2 caddr)
(define operand3 cadddr)

(define exists-operand2?
  (lambda (statement)
    (not (null? (cddr statement)))))

(define exists-operand3?
  (lambda (statement)
    (not (null? (cdddr statement)))))

; these helper functions define the parts of the various statement types
(define class-name cadr)
(define extending-class caddr)
(define class-body cadddr)
(define definition-body cdr)
(define funcall-params cddr)
(define closure-params car)
(define funcall-name cadr)
(define statement-type operator)
(define get-expr operand1)
(define get-declare-var operand1)
(define get-declare-value operand2)
(define exists-declare-value? exists-operand2?)
(define get-assign-lhs operand1)
(define get-assign-rhs operand2)
(define get-condition operand1)
(define get-then operand2)
(define get-else operand3)
(define get-body operand2)
(define super-class car)
(define closure-body cdr)
(define extended-class cadar)
(define exists-else? exists-operand3?)
(define get-try operand1)
(define get-catch operand2)
(define get-finally operand3)
(define fname cadr)
(define params-body cddr)
(define function-body cddr)
(define body cadddr)
(define catch-var operand1)

; for accessing the right part of the input statement with dot and such
(define assign-class cadadr)
(define assign-class-var (lambda (l) (caddr (cadr l))))
(define dot-function-name
  (lambda (statement)
    (car (cddar (cdr statement)))))

;helper functions and abstractions for accessing the environment
(define currentclass
  (lambda (closure)
    (if (not (list? closure))
        closure
        (car closure))))
(define topframe car)
(define remainingframes cdr)

(define firstvariable (lambda (layer) (car (variablelist layer))))
(define firstvalue (lambda (vallist) (unbox (car vallist))))
(define emptylayer? (lambda (layer) (null? (variablelist layer))))
(define emptystate? (lambda (state) (and (emptylayer? (car state)) (null? (cdr state)))))
(define cdrlayer (lambda (state) (list (cdr (variablelist state)) (cdr (valuelist state)))))
(define variablelist car)
(define valuelist cadr)
(define fnamelist car)
(define fcloselist cadr)
(define value?
  (lambda (val)
    (or (or (boolean? val) (number? val)) (not (or (or (pair? val) (null? val)))))))
; Returns the list of variables from a frame
(define variables car)
; Returns the store from a frame
(define store cadr)



