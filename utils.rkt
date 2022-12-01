#lang racket
(require (prefix-in ra: data/ralist) )
(provide (all-defined-out))
(struct literal [symbol phase] #:transparent)

(define  (negate-literal l)
  (struct-copy literal l [phase (not (literal-phase l))]))

(define (choose ls)
  (cond [(vector? ls) (vector-ref ls (random (vector-length ls)))]
        [(list? ls) (list-ref ls (random (length ls)))]
        [(ra:list? ls) (ra:list-ref ls (random (ra:length ls)))]))

(module+ test
  (require rackunit)
  (check-equal? (negate-literal (literal 'var-1 #t))
                (literal 'var-1 #f)))


(define (empty-assignment) empty)
(define (extend-assignment a lit)
  (cons lit a))
(define (assignment-size a)
  (length a))
