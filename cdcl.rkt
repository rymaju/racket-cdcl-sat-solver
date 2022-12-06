#lang racket


;; Data Structures


;; Environment (Env)
;; value : Env Literal -> (U #t #f Undefined)
;; deduce : Env Literal -> Env ;; For unit propagation
;; decide : Env Literal -> Env ;; For deciding variables
;; empty-env : () -> Env
;; level : Env Literal -> Nat
;; backjump : Env Nat -> Env
(require racket/bool "utils.rkt")
(define UNDEFINED 'undefined)
(define undefined? (curry eqv? UNDEFINED))
(struct env (assignment-hash decision-levels unused) #:constructor-name make-env #:transparent)
(define (empty-env) (make-env (hash) (list (set)) (set)))
(define (value env lit)
  (define var-value (hash-ref (env-assignment-hash env)
                              (literal-symbol lit)
                              UNDEFINED))
  (match var-value
    [(== UNDEFINED) UNDEFINED]
    [else (eqv? (literal-phase lit) var-value)]))

(module+ test
  (require rackunit)
  (check-equal? (value (deduce (empty-env) (literal 'x #t))
                       (literal 'x #t))
                #t)
  (check-equal? (value (deduce (empty-env) (literal 'x #f))
                       (literal 'x #t))
                #f)
  (check-equal? (value (deduce (empty-env) (literal 'x #t))
                       (literal 'x #f))
                #f)
  (check-equal? (value (deduce (empty-env) (literal 'x #f))
                       (literal 'x #f))
                #t)
  (check-equal? (value (empty-env) (literal 'x #t))  UNDEFINED))

(define (deduce env0 lit)
  (match-let* ([(env assignment-hash decision-levels unused) env0]
               [`(,current-level . ,lower-levels) decision-levels]
               [(literal var polarity) lit])
    (make-env (hash-set assignment-hash var polarity)
              (cons (set-add current-level var) lower-levels)
              (set-remove unused var))))

(define (decide env0)
  (define unused-vars (env-unused env0))
  (define lower-levels (env-decision-levels env0))
  (values (struct-copy env env0
                       [unused (set-rest env0)]
                       [decision-levels (cons (set) lower-levels)])
          (set-rest unused-vars)))

(define (update-watchers clause-obs env lit)

  )
(define (backjump env l) #f)
(define (level env0 lit)
  (- (length (env-decision-levels env0))
     (index-of (env-decision-levels env0) (literal-symbol lit))))

(define (learn-clause env c) #f)

(struct clause-observer () #:constructor-name make-clause-observer)
(define (add-watcher) 1)
(struct watcher () #:constructor-name make-watcher)
;; Undefined : 'undefined

;; ClauseObserver
;; watchers : ClauseObserver Literal -> (Listof Watcher)
;; add : ClauseObserver Watcher -> ClauseObserver
;; remove : ClauseObserver Watcher -> ClauseObserver
;; clause-watchers : ClauseObserver Clause -> (Listof Watcher)
;; forget :  ClauseObserver -> ClauseObserver
;; learn-clause : ClauseObserver Clause -> ClauseObserver

;; Clause : (Listof Literal)


;; Literal : (literal Var Boolean)
;; Var : Symbol

;; cdcl : CNF -> Boolean
(define (cdcl cnf)
  (match (preprocess cnf)
    [(list obs env) (solve obs env)]
    [#f #f]))

(define (solve clause-obs env0)
  ;; Make a decision
  (define-values (env decision) (decide env0))
  (match (propagate clause-obs env decision)
    [(success clause-obs env) (solve clause-obs env)]
    [(conflict clause-obs env clause)
     (define maybe-resolved-env (resolve-conflict env clause))
     (and maybe-resolved-env (solve clause-obs maybe-resolved-env))]))



(struct success (clause-obs env))
(struct conflict (clause-obs env conlflict-clause))

(define (propagate clause-obs env decision [literals-to-assign (list decision)])
  (match literals-to-assign
    [`() (success clause-obs env)]
    [`(,lit . ,next)
     (define env+ (deduce env lit))
     (match (update-watchers clause-obs env+ lit)
       ;; what extra things to add to stack of assgns
       ;; new clause state
       ;; if unsat
       [(list clause-obs deductions)
        (propagate clause-obs env+ decision (append deductions next))]
       [#f #f])]))


(define (resolve-conflict env clause)
  (define first-conflict-literal (first clause))
  (define env/backjump (backjump (level env first-conflict-literal)))
  (define conflict-clause-  (map negate-literal clause))
  (define env/learned-conflict-clause- (learn-clause env/backjump conflict-clause-))
  env/learned-conflict-clause-)




;; CNF -> (U (Listof ClauseObserver Env) #f)
(define (preprocess cnf)
  (define init-obs (make-clause-observer))
  (define init-env (empty-env))
  (for/fold ([obs init-obs]
             [env init-env]
             [found-empty-clause #f]
             #:result (and (not found-empty-clause)
                           (list obs env)))
            ([clause (in-list cnf)]
             #:break found-empty-clause)
    (match clause
      [`(,l1 ,l2 . ,_)
       (define obs/l1 (add-watcher obs (make-watcher l1 clause)))
       (define obs/l2 (add-watcher obs (make-watcher l2 clause)))
       obs/l2]
      [`(,l1)
       (define env/unit-assignment (deduce env l1))
       1]
      [`() (values 'whatever 'whatever #t)])))
