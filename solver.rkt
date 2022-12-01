#lang errortrace racket
(require (prefix-in ra: data/ralist) "utils.rkt")

(provide dpll)

;; Tombstone
(define REMOVED-CLAUSE 'REMOVED-CLAUSE)
(define (removed-clause? e) (equal? REMOVED-CLAUSE e))

(define (dpll cnf0 [assignment (empty-assignment)])
  (define cnf (apply ra:list cnf0))
  (define watched-literals (build-watched-literals cnf))
  (define unused-vars (list->set (hash-keys watched-literals)))
  (dpll^ cnf assignment watched-literals unused-vars))

(define (dpll^ cnf0 assignment watched-literals unused-vars)
  (define cnf (if (cons? assignment) (simplify cnf0 (car assignment) watched-literals) cnf0))
  (cond [(found-empty-clause? cnf) #f]
        [(contains-unit-clause? cnf)
         => (lambda (unit-lit) (dpll^ cnf (extend-assignment assignment unit-lit) watched-literals unused-vars))]
        [(set-empty? unused-vars) #t]
        [else (choose-literal-and-recur cnf assignment watched-literals unused-vars)]))

(define FOUND-EMPTY-CLAUSE 'FOUND-EMPTY-CLAUSE)
(define (found-empty-clause? cnf)
  (equal? FOUND-EMPTY-CLAUSE cnf))

(define (simplify cnf next-literal watched-literals)
  (for/fold ([simplified cnf])
            ([clause-idx (in-set (hash-ref watched-literals (literal-symbol next-literal)))]
             #:break (found-empty-clause? simplified)
             #:do [(define clause (formula-ref cnf clause-idx))])
    (cond [(removed-clause? clause) simplified]
          [(clause-contains? clause next-literal) (formula-set simplified clause-idx REMOVED-CLAUSE)]
          [else
           (define clause^ (remove (negate-literal next-literal) clause))
           (if (empty? clause^)
               'FOUND-EMPTY-CLAUSE
               (formula-set simplified clause-idx clause^))])))


(define (choose-literal-and-recur cnf assignment watched-literals unused-vars)
  (define-values (var unused-vars^) (choose-unused-var unused-vars))
  (or (dpll^ cnf (extend-assignment assignment (literal var #t)) watched-literals unused-vars^)
      (dpll^ cnf (extend-assignment assignment (literal var #f)) watched-literals unused-vars^)))

(define (choose-unused-var unused-vars)
  (values (set-first unused-vars) (set-rest unused-vars)))

(define (clause-contains? clause lit)
  (member lit clause))

(define (contains-empty-clause? cnf)
  (for/or ([clause (ra:in-list cnf)])
    (empty? clause)))

(define (contains-unit-clause? cnf)
  (for/first ([clause (ra:in-list cnf)]
              #:when (and (cons? clause) (= (length clause) 1)))
     (car clause)))


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


(define (build-watched-literals cnf)
  (for/fold ([watched-literals (hash)])
            ([clause (in-formula cnf)]
             [idx (in-naturals)])
    (for/fold ([watched-literals:clause watched-literals])
              ([lit (in-list clause)])
      (hash-update watched-literals:clause
                   (literal-symbol lit)
                   (λ (cls-idx-set) (set-add cls-idx-set idx))
                   (λ () (set idx))))))
