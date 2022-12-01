#lang errortrace racket
(require (prefix-in ra: data/ralist) "utils.rkt")

(provide dpll)


(define (empty-assignment) (list))
(define (extend-assignment a lit)
  (cons lit a))
(define (assignment-size a)
  (length a))

(define (dpll cnf0 [assignment (empty-assignment)])
  (define ralist (apply ra:list cnf0))
  (dpll^ ralist assignment (build-watched-literals ralist)))

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



(define (dpll^ cnf0 assignment watched-literals)

  (define cnf (if (cons? assignment)
                  (simplify cnf0
                            (car assignment)
                            (get-relevant-clause-idxes
                             watched-literals
                             (literal-symbol (car assignment))))
                  cnf0))
  (cond [(contains-empty-clause? cnf) #f]
        [(contains-unit-clause? cnf watched-literals) => (λ (unit-lit)
                                          (dpll^ cnf
                                                 (extend-assignment assignment unit-lit)
                                                 watched-literals))]
        [(or (formula-empty? cnf)
             (= (assignment-size assignment) (hash-count watched-literals)) ) #t]
        [else (choose-literal-and-recur cnf assignment watched-literals)]))

(define (get-relevant-clause-idxes watched-literals lit-sym)
  (hash-ref watched-literals lit-sym (set)))

(define (simplify cnf next-literal relevant-clause-idx*)
  (for/fold ([simplified cnf])
            ([idx (in-set relevant-clause-idx*)]
             #:do[(define clause (formula-ref cnf idx))])
    ;; damn, vector set...
    ;; use okazaki?
    (formula-set simplified idx (and clause
                              (clause-contains? clause next-literal)
                              (remove (negate-literal next-literal) clause)))))

(define (clause-contains? clause lit)
  (member lit clause))

;; TODO fails
(define (contains-empty-clause? cnf)
  (for/or ([clause (in-formula cnf)])
    (empty? clause)))

(define (contains-unit-clause? cnf _)
  (for/or ([clause (in-formula cnf)])
    (and clause (= (length clause) 1) (car clause))))





(define (choose-literal-and-recur cnf assignment watched-literals)
  (define sym (set-first (set-subtract (list->set (hash-keys watched-literals))
                                     (list->set (map literal-symbol assignment)))))
  (or (dpll^ cnf
             (extend-assignment assignment (literal sym #t))
             watched-literals)
      (dpll^ cnf
             (extend-assignment assignment (literal sym #f))
             watched-literals)))


(define (formula-set f idx clause)
  (ra:list-set f idx clause))

(define (in-formula f)
  (ra:in-list f))

(define (formula-ref f idx)
  (ra:list-ref f idx))

(define (formula-empty? f) (ra:empty? f))
(define (formula-length f) (ra:length f))
