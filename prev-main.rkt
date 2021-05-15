#lang racket
(require "functionParser.rkt")

;;;;; *************************************************
;;;;; CSDS 345: PLC
;;;;; Simple Language Interpreter Project
;;;;; By Joanna Elia, Sasha Wallace, William Turner
;;;;; *************************************************

;;;; state is saved in a list with a variable list and a value list
;;;;     it uses escape value if value was just declared and not assigned

;;; start function needed from assignment that takes a filename, calls parser with the filename,
;;;       evaluates the syntax tree returned by parser, and returns the proper value

; for our tests call (interpret "tests\\test1")
(define interpret
  (lambda (filename)
    (display (parser filename)) (newline)
    (Main (parser filename) (newlayer '()))))


;;; checks Mstate for each statement in the list until there is a returnvalue
(define Main (lambda (lis state)
               (call/cc (lambda (return)
                          (Main (followingstatements lis) (Mstate (firststatement lis) state return (lambda (v) v) (lambda (v) (error 'illegal-break)) (lambda (v) (error 'illegal-throw))))))))

;;; handles any function that can alter the state
(define Mstate (lambda (statement state return next break throw)
                 (cond
                   ((eq? (firststatement statement) 'var)       (declare (followingstatements statement) state))
                   ((eq? (firststatement statement) '=)         (assign (followingstatements statement) state))
                   ((eq? (firststatement statement) 'if)        (if* (followingstatements statement) state return next break throw))
                   ((eq? (firststatement statement) 'while)     (call/cc (lambda (break) (while* (followingstatements statement) state return break throw))))
                   ((eq? (firststatement statement) 'return)    (return (evaluate (cadr statement) state)))
                   ((eq? (firststatement statement) 'begin)     (begin (followingstatements statement) (newlayer state) return next break throw))
                   ((eq? (firststatement statement) 'continue)  (next (removefirstlayer state)))
                   ((eq? (firststatement statement) 'break)     (break (removefirstlayer state)))
                   ((eq? (firststatement statement) 'try)       (try statement (newlayer state) return next break throw))
                   ((eq? (firststatement statement) 'throw)     (throw (cadr statement)))
                   (else                                        (error 'invalid-sytax))
                   )))

;;; handles try statements
(define try
  (lambda (statement state return next break throw)
      (begin (findtry statement) state return (lambda (v) (begin (findfinally statement) v return next break throw)) (lambda (v) (begin (findfinally statement) v return break break throw))
             (lambda (v) (begin (findcatch statement) (declareVar (caar (findcatch statement)) v (newlayer (removefirstlayer state))) return next break throw)))))

;;; locates catch statement
(define findcatch
  (lambda (statement)
    (cond
      ((null? (caddr statement)) (null))
      (else (cdaddr statement)))))
      
;;; locates finally statement                                
(define findfinally
  (lambda (statement)
    (cond
      ((null? (cadddr statement)) null)
      (else (cadr (cadddr statement))))))

(define findtry cadr)

(define begin
  (lambda (statement state return next break throw)
    (cond
      ((null? (firststatement statement)) state)
      ((null? (followingstatements statement)) (removefirstlayer (Mstate (firststatement statement) state return next break throw)))
      (else (begin (followingstatements statement) (Mstate (firststatement statement) state return next break throw) return next break throw)))))

;;; declares varaiable and assigns to null or a given value, throws error if redefining the state
(define declare
  (lambda (declareparameters state)
    (cond
      ((declaredinlayer? (variable declareparameters) (firstlayer state))   (error 'redefined-variable))
      ((justdeclare? declareparameters)                 (declareVar (variable declareparameters) 'null state))
      (else                                             (declareVar (variable declareparameters) (evaluate (valueExpression declareparameters) state) state)))))


;;; sets variable to assigned value, throws error if variable wasned declared
(define assign
  (lambda (assignparameters state)
    (if (declared?* (variable assignparameters) state)
        (assignValue (variable assignparameters) (evaluate (valueExpression assignparameters) state) state (lambda (v) v))
        (error 'using-before-declaring))))


;;; returns Mstate with proper statement executed or original state depending on boolean value of the condition and presence or absence of else clause
(define if* (lambda (statement state return next break throw)
              (cond
                ((evaluate (condition statement) state) (Mstate (iftruestatement statement) state return next break throw))
                ((elsenotpresent statement) state)
                (else (Mstate (iffalsestatement statement) state return next break throw))
              )))

;;; returns Mstate for after the loop body has ran the requisite number of times
(define while* (lambda (statement state return break throw)
                 (cond
                   ((evaluate (condition statement) state) (while* statement (call/cc (lambda (next) (Mstate (whilebody statement) state return next break throw))) return break throw))
                   (else state)
                   )))

;;; evaluates any expression. m_value and m_boolean. throws error if encouters unknown operator
(define evaluate
  (lambda (expression state)
    (cond
      ((number? expression)                  expression)
      ((isboolean? expression)               (toboolean expression))
      ((variable? expression)                (getValue* expression state))
      ((and (eq? (operator expression) '-) (norightoperand? expression)) ;unary -
                                             (* -1 (evaluate (leftoperand expression) state)))     
      ((eq? (operator expression) '+)        (+ (evaluate (leftoperand expression) state) (evaluate (rightoperand expression) state)))
      ((eq? (operator expression) '-)        (- (evaluate (leftoperand expression) state) (evaluate (rightoperand expression) state)))
      ((eq? (operator expression) '*)        (* (evaluate (leftoperand expression) state) (evaluate (rightoperand expression) state)))
      ((eq? (operator expression) '/)        (quotient (evaluate (leftoperand expression) state) (evaluate (rightoperand expression) state)))
      ((eq? (operator expression) '%)        (remainder (evaluate (leftoperand expression) state) (evaluate (rightoperand expression) state)))
      ((eq? (operator expression) '&&)       (and (evaluate (leftoperand expression) state) (evaluate (rightoperand expression) state)))
      ((eq? (operator expression) '||)       (or (evaluate (leftoperand expression) state) (evaluate (rightoperand expression) state)))
      ((eq? (operator expression) '!)        (not (evaluate (leftoperand expression) state)))
      ((eq? (operator expression) '==)       (eq? (evaluate (leftoperand expression) state) (evaluate (rightoperand expression) state)))
      ((eq? (operator expression) '<)        (< (evaluate (leftoperand expression) state) (evaluate (rightoperand expression) state)))
      ((eq? (operator expression) '>)        (> (evaluate (leftoperand expression) state) (evaluate (rightoperand expression) state)))
      ((eq? (operator expression) '<=)       (<= (evaluate (leftoperand expression) state) (evaluate (rightoperand expression) state)))
      ((eq? (operator expression) '>=)       (>= (evaluate (leftoperand expression) state) (evaluate (rightoperand expression) state)))
      ((eq? (operator expression) '!=)       (not (= (evaluate (leftoperand expression) state) (evaluate (rightoperand expression) state))))
      (else                                  (error 'bad-operator)))))



;;;;; ****************************Abstraction ****************************************************
;;; state manipulation
;returns first layer of state
(define firstlayer
  (lambda (state)
    (car state)))

; returns state with a copy of the previous first layer added as a new layer
(define newlayer (lambda (state)
                   (cons '(() ()) state)))

; returns state with the first layer removed
(define removefirstlayer (lambda (state)
                           (cond
                             ((or (equal? (car state) 'continue) (equal? (car state) 'break)) (cons (car state) (cdr (cdr state))))
                             (else (cdr state))
                             )
                        ))

;;; gets value of variable from entire state
(define getValue*
  (lambda (var state)
    (cond
      ((not (declared?* var state)) (error 'using-before-declaring))
      ((declaredinlayer? var (firstlayer state)) (getValueLayer var (firstlayer state)))
      (else (getValue* var (cdr state))))))
;;; returns value of given variable or throws error if variable wasn't declared
(define getValueLayer
  (lambda (var layer)
    (cond
      ((emptylayer? layer)                                                     (error 'using-before-declaring))
      ((and (eq? var (firstvariable layer)) (unassigned? (firstvalue layer)))  (error 'using-before-assigning))
      ((eq? var (firstvariable layer))                                         (firstvalue layer))
      (else                                                                    (getValueLayer var (cdrlayer layer))))))

;;; declared? for a state with layers
(define declared?*
  (lambda (var state)
    (cond
      ((emptystate? state) #f)
      ((declaredinlayer? var (firstlayer state)) #t)
      ((null? (cdr state)) #f)
      (else (declared?* var (cdr state))))))
;;; checks if a variable was declared; can be unassigned
(define declaredinlayer?
  (lambda (var layer)
    (cond
      ((emptylayer? layer)             #f)
      ((eq? var (firstvariable layer)) #t)
      (else                            (declaredinlayer? var (cdrlayer layer))))))

;;; searches through entire state layer by layer to assign a value to an already declared variable
(define assignValue
  (lambda (var newVal state return)
    (cond
      ((not (declared?* var state)) (error 'using-before-declaring))
      ((declaredinlayer? var (firstlayer state)) (return (declareVar var newVal state)))
      (else (assignValue var newVal (cdr state) (lambda (v) (return (cons (firstlayer state) v))))))))

(define declareVar
  (lambda (var newVal state)
    (updatefirstvalue (setValueinLayer var newVal (firstlayer state) (lambda (v) v)) state)))
;;; sets a value to a variable, first searches through to see if variable is already present and updates if necessary, adds new var to state otherwise
(define setValueinLayer
  (lambda (var newval layer return)
    (cond
      ((emptylayer? layer)             (return (combinelists (addtolist var (variablelist layer)) (addtolist newval (valuelist layer)))))
      ((eq? (firstvariable layer) var) (return (combinelists (variablelist layer) (updatefirstvalue newval (valuelist layer)))))
      (else                            (setValueinLayer var newval (cdrlayer layer) (lambda (v) (return (combinelists (addtolist (firstvariable layer)
                                                                   (variablelist v)) (addtolist (firstvalue layer) (valuelist v))))))))))



(define variablelist (lambda (layer) (car layer)))
(define valuelist (lambda (layer) (car (cdr layer))))
(define firstvariable (lambda (layer) (car (variablelist layer))))
(define firstvalue (lambda (layer) (car (valuelist layer))))
(define emptylayer? (lambda (layer) (null? (variablelist layer))))
(define emptystate? (lambda (state) (and (emptylayer? (firstlayer state)) (null? (cdr state)))))
;;returns the state without the first variable and first value
(define cdrlayer (lambda (state) (list (cdr (variablelist state)) (cdr (valuelist state)))))

;; checks if a value is unassigned
(define unassigned? (lambda (val) (eqv? val 'null)))

(define addtolist cons)
(define updatefirstvalue (lambda (val state) (cons val (cdr state))))
(define combinelists list)

;;; checks if given is a variable,
;;;        with rules that it is not a pair nor null nor a number
(define variable?
  (lambda (var)
    (not (or (or (pair? var) (null? var)) (number? var)))))

; first statement in a list
(define firststatement (lambda (lis) (car lis)))
; following statements in a list
(define followingstatements (lambda (lis) (cdr lis)))
; condition of an if or while states when passed to if* or while*
(define condition (lambda (lis) (car lis)))
; statement to execute when true
(define iftruestatement (lambda (lis) (cadr lis)))
; statement to execute when false
(define iffalsestatement (lambda (lis) (caddr lis)))
; whether or not there is an else clause present
(define elsenotpresent (lambda (lis) (null? (cddr lis))))
; body of a while loop
(define whilebody (lambda (lis) (cadr lis)))

;;;; for evaluate
(define operator car)
(define leftoperand cadr)
(define rightoperand caddr)

;;; checks if a right operand is present
(define norightoperand?
  (lambda (lis)
    (null? (cdr (cdr lis)))))

;;; checks if a value is a boolean or not, including cases for words
(define isboolean?
  (lambda (val)
    (cond
      ((boolean? val) #t)
      ((eq? val 'false) #t)
      ((eq? val 'true) #t)
      (else #f))))

;;; converts 'true to #t and 'false to #f
(define toboolean
  (lambda (val)
    (cond
      ((boolean? val) val)
      ((eq? val 'false) #f)
      ((eq? val 'true) #t)
      (else (error 'wrong-type)))))

;;; changes a #t to true, #f to false for the final returned value
(define toword
  (lambda (val)
    (cond 
        ((and (boolean? val) val) 'true)
        ((boolean? val) 'false)
        (else val))))

;;; checks if variable should be declared (true) or declared and assigned (false)
(define justdeclare?
  (lambda (parameters)
    (null? (cdr parameters))))

;;; returns variable for declare and assign
(define variable
  (lambda (parameters)
    (car parameters)))

;;; returns the value or expression for declare and assign
(define valueExpression
  (lambda (parameters)
    (cadr parameters)))

; testing lines

;(interpret "tests\\test1")
;(interpret "tests\\test2")
;(interpret "tests\\test3")
;(interpret "tests\\test4")
;(interpret "tests\\test6")
;(interpret "tests\\test8")
;(interpret "tests\\test9")
;(interpret "tests\\test11")
;(interpret "tests\\test12")
;(interpret "tests\\test13")
;(interpret "tests\\test14")
;(interpret "tests\\test5")
