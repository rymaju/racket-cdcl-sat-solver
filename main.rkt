#lang racket
(require "utils.rkt" "solver.rkt")
(module+ test (require rackunit))

;; takes a simplified dimacs (without header or ending zero) and converts it into our literals
(define (simp-dimacs->cnf dimacs)
  (for/list ([clause (in-list dimacs)])
    (for/list ([integer (in-list clause)])
      (literal (string->symbol (format "var-~a" (abs integer))) (positive? integer)))))


(module+ test
  (check-equal? (simp-dimacs->cnf '((1 2) (-2 3)))
                (list (list (literal 'var-1 #t) (literal 'var-2 #t))
                      (list (literal 'var-2 #f) (literal 'var-3 #t)))))


;; is this CNF SAT according to Rosette?
(define (rosette-sat? cnf)
  (eval (rosette-compile cnf)))

(module+ test
  (check-true (rosette-sat? (simp-dimacs->cnf '((1 2) (-2 3))))))

;; Compiles CNF into a quoted racket expression to `eval`
;; Uses rosette to determine if CNF is SAT
(define (rosette-compile cnf)
  (define all-vars (remove-duplicates (map literal-symbol (flatten cnf))))
  `(begin (require rosette)
          (define-symbolic ,@all-vars boolean?)
          (define sol (solve (assert (and ,@(for/list ([clause (in-list cnf)])
                                  `(or ,@(for/list ([lit (in-list clause)])
                                           (if (literal-phase lit)
                                               (literal-symbol lit)
                                               `(not ,(literal-symbol lit))))))))))
          ;(displayln (complete-solution sol (list ,@all-vars)))
          (sat? sol)))

(module+ test
  (check-equal? (rosette-compile (simp-dimacs->cnf '((1 2) (-2 3))))
                '(begin
                   (require rosette)
                   (define-symbolic var-1 var-2 var-3 boolean?)
                   (define sol (solve (assert (and (or var-1 var-2) (or (not var-2) var-3)))))
                   (sat? sol))))


(module+ test

  (define DIMACS-SAT-1
    '((1 2)
      (-2 -4)
      (3 4)
      (-4 -5)
      (5 -6)
      (6 -7)
      (6 7)
      (7 -16)
      (8 -9)
      (-8 -14)
      (9 1)
      (9 -1)
      (-1 -11)
      (1 12)
      (11 12)
      (13 14)
      (14 -15)
      (15 16)))
  (define DIMACS-SAT-2 '((1 2) (-2 3)))

  (define DIMACS-UNSAT-1
    '((1 2)
      (-2 -4)
      (3 4)
      (-4 -5)
      (5 -6)
      (6 -7)
      (6 7)
      (7 -16)
      (8 -9)
      (-8 -14)
      (9 1)
      (9 -1)
      (-1 -11)
      (1 12)
      (11 12)
      (13 14)
      (14 -15)
      (15 16)
      (-2)
      (2)))

  (define DIMACS-UNSAT-2 '((-1) (1)))



  (check-true (rosette-sat? (simp-dimacs->cnf DIMACS-SAT-1)))
  (check-true (dpll (simp-dimacs->cnf DIMACS-SAT-1)))

  (check-true (rosette-sat? (simp-dimacs->cnf DIMACS-SAT-2)))
  (check-true (dpll (simp-dimacs->cnf DIMACS-SAT-2)))

  (check-false (rosette-sat? (simp-dimacs->cnf  DIMACS-UNSAT-1)))
  (check-false (dpll (simp-dimacs->cnf  DIMACS-UNSAT-1)))

  (check-false (rosette-sat? (simp-dimacs->cnf  DIMACS-UNSAT-2)))
  (check-false (dpll (simp-dimacs->cnf  DIMACS-UNSAT-2)))

  #;(for ([i (in-range 10)])
    (define test (simp-dimacs->cnf (gen-random-case i 100 10)))
    (check-equal? (dpll test) (rosette-sat? test)))

  (displayln "Time for DPLL on true random:")
  (time   (dpll (simp-dimacs->cnf (gen-random-case 42 20000 10))))

  (check-true (time-on-chosen-benchmarks (list dpll))))


(define (file->cnf path)
  (define zero-ended-clauses (cdr (file->lines path)))

  (define simp-dimacs
    (for/list ([dimacs-cls-str (in-list zero-ended-clauses)])
      (map string->number (drop-right (string-split dimacs-cls-str) 1))))
  (simp-dimacs->cnf simp-dimacs))

(define (time-on-chosen-benchmarks solver*)
  (define paths '("./chosen-benchmarks/9a296539e33398c9ae36663371a63b39-randomG-Mix-n17-d05.cnf"
                  "./chosen-benchmarks/951a20a37a23488001f3aa2fa53e6baa-randomG-n16-d05.cnf"
                  "./chosen-benchmarks/1527378fc216e0506bf8b63d0fad56be-randomG-Mix-n18-d05.cnf"
                  ;"./chosen-benchmarks/d5453d6d31f33a310ce34ee4bcfcbe50-prime_a24_b24.cnf"
                  ;"./chosen-benchmarks/50468d740d0d9cd69c43e4122014d60e-sted6_0x1e3-97.cnf"
                  ;"./chosen-benchmarks/c1484d43c95d76184dbe50ac5fc98854-satch2ways17w.cnf"
                  ))
  (for/and ([path (in-list paths)])
    (displayln (format "--- START Test ~a ---" path))
    (define results
      (for/list ([solver (in-list solver*)]
                 [idx (in-naturals)])
        (displayln (format "Solver ~a:" idx))
        (time (solver (file->cnf path)))))
     (displayln (format "--- END Test ~a ---" path))
    (or (<= (length results) 1) (apply equal? results))))


(define (gen-random-case seed nclauses csize)
  (random-seed seed)
  (for/list ([_ (in-range nclauses)])
    (for/list ([_ (in-range csize)])
      (if (= (random 2) 0)
          (add1 (random 100))
          (- -1 (random 100))))))
