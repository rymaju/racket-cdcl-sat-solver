#lang racket
(require (prefix-in ra: data/ralist) "utils.rkt")

(provide dpll)

(define (dpll cnf0 [assignment (empty-assignment)])
  (dpll^ (apply ra:list cnf0) assignment))

(define (dpll^ cnf0 [assignment (empty-assignment)])
  (define cnf (if (cons? assignment) (simplify cnf0 (car assignment)) cnf0))
  (cond [(contains-empty-clause? cnf) #f]
        [(contains-unit-clause? cnf)
         => (lambda (unit-lit) (dpll^ cnf (extend-assignment assignment unit-lit)))]
        [(or (= (assignment-size assignment) (ra:length cnf)) (ra:empty? cnf)) #t]
        [else (choose-literal-and-recur cnf assignment)]))

(define (simplify cnf next-literal)
  (ra:for/list ([clause (ra:in-list cnf)]
                #:unless (clause-contains? clause next-literal))
               (remove (negate-literal next-literal) clause)))

(define (clause-contains? clause lit)
  (member lit clause))

(define (contains-empty-clause? cnf)
  (for/or ([clause (ra:in-list cnf)])
    (empty? clause)))

(define (contains-unit-clause? cnf)
  (for/or ([clause (ra:in-list cnf)])
    (and (= (length clause) 1) (car clause))))



(define (choose-literal-and-recur cnf assignment)
  (define l (choose-literal cnf))
  (or (dpll^ cnf (extend-assignment assignment l))
      (dpll^ cnf (extend-assignment assignment (negate-literal l)))))

(define (choose-literal cnf)
  (choose (choose cnf)))


(define (formula-set f idx clause)
  (ra:list-set f idx clause))

(define (in-formula f)
  (ra:in-list f))

(define (formula-ref f idx)
  (ra:list-ref f idx))

(define (formula-empty? f) (ra:empty? f))
(define (formula-length f) (ra:length f))
