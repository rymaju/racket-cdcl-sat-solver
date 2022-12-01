#lang racket
(module+ test (require rackunit))

(struct literal [symbol phase] #:transparent)

(define  (negate-literal l)
  (struct-copy literal l [phase (not (literal-phase l))]))

(define (choose ls)
  (list-ref ls (random (length ls))))

(module+ test
  (check-equal? (negate-literal (literal 'var-1 #t))
                (literal 'var-1 #f)))



(define (dpll cnf)
  (cond [(contains-unit-clause? cnf) => (lambda (unit-lit) (dpll (unit-propagate cnf unit-lit)))]
        ;[(contains-pure-literal?) (assign-pure-literal cnf)]
        [(empty? cnf) #t]
        [(ormap empty? cnf) #f]
        [else (choose-literal-and-recur cnf)]))

(define (contains-unit-clause? cnf)
  (for/or ([clause (in-list cnf)])
    (and (= (length clause) 1) (car clause))))

(define (unit-propagate cnf lit)
  (for/list ([clause (in-list cnf)]
             #:unless (member lit clause))
    (if (equal? clause (list lit))
        clause
        (remove (negate-literal lit) clause))))

(define (clause-has-negation? clause lit)
  (member (negate-literal lit) clause))


(define (choose-literal-and-recur cnf)
  (define l (choose-literal cnf))
  (or (dpll (cons (list l) cnf))
      (dpll (cons (list (negate-literal l)) cnf))))

(define (choose-literal cnf)
  (choose (choose cnf)))

;; takes a simplified dimacs (without header or ending zero) and converts it into our literals
(define (simp-dimacs->cnf dimacs)
  (for/list ([clause (in-list dimacs)])
    (for/list ([integer (in-list clause)])
      (literal (string->symbol (format "var-~a" (abs integer))) (positive? integer)))))

(define CNF-SAT-1 (simp-dimacs->cnf '((1 2) (-2 3))))


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
          (sat? (solve (begin ,@(for/list ([clause (in-list cnf)])
                                  `(or ,@(for/list ([lit (in-list clause)])
                                           (if (literal-phase lit)
                                               (literal-symbol lit)
                                               `(not ,(literal-symbol lit)))))))))))

(module+ test
  (check-equal? (rosette-compile (simp-dimacs->cnf '((1 2) (-2 3))))
                '(begin
                   (require rosette)
                   (define-symbolic var-1 var-2 var-3 boolean?)
                   (sat? (solve (begin (or var-1 var-2) (or (not var-2) var-3)))))))


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

  (check-true (rosette-sat? (simp-dimacs->cnf DIMACS-SAT-1)))
  (check-true (dpll (simp-dimacs->cnf DIMACS-SAT-1)))
  #;(time-on-chosen-benchmarks rosette-sat? dpll))


(define (file->cnf path)
  (define zero-ended-clauses (cdr (file->lines path)))

  (define simp-dimacs
    (for/list ([dimacs-cls-str (in-list zero-ended-clauses)])
      (map string->number (drop-right (string-split dimacs-cls-str) 1))))
  (simp-dimacs->cnf simp-dimacs))

(define (time-on-chosen-benchmarks solver1 solver2)
  (define paths '("./chosen-benchmarks/9a296539e33398c9ae36663371a63b39-randomG-Mix-n17-d05.cnf"
                  "./chosen-benchmarks/951a20a37a23488001f3aa2fa53e6baa-randomG-n16-d05.cnf"
                  "./chosen-benchmarks/1527378fc216e0506bf8b63d0fad56be-randomG-Mix-n18-d05.cnf"
                  "./chosen-benchmarks/d5453d6d31f33a310ce34ee4bcfcbe50-prime_a24_b24.cnf"
                  "./chosen-benchmarks/50468d740d0d9cd69c43e4122014d60e-sted6_0x1e3-97.cnf"
                  "./chosen-benchmarks/c1484d43c95d76184dbe50ac5fc98854-satch2ways17w.cnf"))
  (for ([path (in-list paths)])
    (displayln (format "Test ~a:" path))
    (displayln "Solver 1:")
    (define ans1 (time (solver1 (file->cnf path))))
    (displayln "Solver 2:")
    (define ans2 (time (solver2 (file->cnf path))))
    (unless (equal? ans1 ans2) (error (format "~a =/= ~a") ans1 ans2))))
