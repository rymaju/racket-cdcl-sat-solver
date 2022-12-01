#lang racket

(provide (all-defined-out))

(struct literal [symbol phase] #:transparent)

(define  (negate-literal l)
  (struct-copy literal l [phase (not (literal-phase l))]))

(define (choose ls)
  (cond [(vector? ls) (vector-ref ls (random (vector-length ls)))]
        [(list? ls) (list-ref ls (random (length ls)))]))

(module+ test
  (require rackunit)
  (check-equal? (negate-literal (literal 'var-1 #t))
                (literal 'var-1 #f)))


;; takes a simplified dimacs (without header or ending zero) and converts it into our literals
(define (simp-dimacs->cnf dimacs)
  (for/list ([clause (in-list dimacs)])
    (for/list ([integer (in-list clause)])
      (literal (string->symbol (format "var-~a" (abs integer))) (positive? integer)))))

(module+ test
  (check-equal? (simp-dimacs->cnf '((1 2) (-2 3)))
                (list (list (literal 'var-1 #t) (literal 'var-2 #t))
                      (list (literal 'var-2 #f) (literal 'var-3 #t)))))
