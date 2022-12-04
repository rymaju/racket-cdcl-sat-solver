#lang errortrace racket
(require (prefix-in ra: data/ralist) "utils.rkt")

(provide dpll)


(define REMOVED-CLAUSE 'REMOVED-CLAUSE)
(define (removed-clause? e) (equal? REMOVED-CLAUSE e))

(define (dpll cnf0)
  (define cnf (apply ra:list cnf0))

  (define-values (watched-literals assignment-set found-contradiction) (build-watched-literals cnf))
  (cond [found-contradiction #f] ;; this is a conflict arising before any simplification even starts
        [else

         (define assignment (set->list assignment-set))
         (define unused-vars (list->set (hash-keys watched-literals)))

         ;; (displayln cnf0)
         ;; (displayln assignment)
         ;; (displayln "————————")
         (dpll^ cnf assignment watched-literals unused-vars)]))

(define (dpll^ cnf assignment0 watched-literals unused-vars)

  (define-values (found-empty-clause watched-literals+ assignment unused-vars+)
    (if (cons? assignment0)
        (simplify* cnf (car assignment0) watched-literals assignment0 unused-vars)
        (values #f watched-literals '() unused-vars)))

  (cond [found-empty-clause #f]
        [(set-empty? unused-vars) #t]
        [else (choose-literal-and-recur cnf assignment watched-literals+ unused-vars+)]))



(define (simplify* cnf next-literal watched-literals assignment unused-vars [deduced-assignments '()])
  (define-values (found-empty-clause watched-literals+ unit-literals)
    (simplify cnf (car assignment) watched-literals assignment))
  (define deduced-assignments+ (append unit-literals deduced-assignments))
  (define unused-vars+ (set-subtract  unused-vars (list->set unit-literals)))

  (if (or found-empty-clause (empty? deduced-assignments+))
      (values found-empty-clause watched-literals+ assignment unused-vars+)
      (let
        ([assignment+ (cons (first deduced-assignments) assignment)])
          (simplify* cnf (first deduced-assignments) watched-literals
                     assignment+ (rest deduced-assignments)))))

(define (simplify cnf next-literal watched-literals assignment)
  ;; (displayln "assignment:")
  ;; (displayln assignment)
  ;; (displayln "watched literals:")
  ;; (displayln watched-literals)
  (for/fold ([found-unsat-clause #f]
             [watched-literals watched-literals]
             [next-unit-propagate* '()])
            ([clause-idx (in-set (hash-ref watched-literals (literal-symbol next-literal) '()))]
             #:break found-unsat-clause
             #:do [(define clause (formula-ref cnf clause-idx))])
    (define-values
      (unassigned
       already-satisfied)
      (for/fold ([unassigned '()]
                 [already-satisfied #f])
                ([lit (in-list clause)]
                 #:do [(define val (literal-value lit assignment))]
                 #:break (or already-satisfied (> (length unassigned) 2)))
        (match val
          ['undefined (values (cons lit unassigned) already-satisfied)]
          [#t (values unassigned #t)]
          [#f (values unassigned already-satisfied)])))

    (cond [already-satisfied
           (values #f watched-literals next-unit-propagate*)]
          ; Remove this clause from the watchlist that brought us here, add it to a watchlist of different literal.
          [(> (length unassigned) 2)
           (let* ([watched-literals (hash-update watched-literals
                                                  (literal-symbol next-literal)
                                                  (λ (c*) (set-remove c* clause-idx)))]
                  [watched-literals (hash-update watched-literals
                                                 (first unassigned)
                                                 (λ (c*) (set-add c* clause-idx)))]
                  [watched-literals (hash-update watched-literals
                                                 (second unassigned)
                                                 (λ (c*) (set-add c* clause-idx)))])
             (values #f watched-literals next-unit-propagate*))]
          [(= (length unassigned) 1)
           (values #f watched-literals (cons (first unassigned) next-unit-propagate*))]
          ; all false: unsat
          [else
           ;; (displayln "Found clause with all false:")
           ;; (displayln clause)
           ;; (displayln (map (curryr literal-value assignment) clause))
           ;; (displayln assignment)
           (values #t watched-literals  next-unit-propagate*)])


    #;(cond [(removed-clause? clause) (values simplified next-unit-propagate)] ;; skip basically
          [(clause-contains? clause next-literal)
           (values
            (formula-set simplified clause-idx REMOVED-CLAUSE)
            next-unit-propagate)]
          [else
           (define clause^ (remove (negate-literal next-literal) clause))
           (cond [(empty? clause^)
                  (values 'FOUND-EMPTY-CLAUSE
                          next-unit-propagate)]
                 [(empty? (cdr clause^))
                  (values (formula-set simplified clause-idx clause^)
                          (car clause^))]
                 [else (values (formula-set simplified clause-idx clause^)
                               next-unit-propagate)])])))


(define (choose-literal-and-recur cnf assignment watched-literals unused-vars)
  (define-values (var unused-vars^) (choose-unused-var unused-vars))
  ;;(displayln (format "Deciding var: ~a = #t" var))
  (or (dpll^ cnf (extend-assignment assignment (literal-positive var)) watched-literals unused-vars^)
;;      (begin  (displayln (format "Backtracking var: ~a = #f" var)) #t)
      (dpll^ cnf (extend-assignment assignment (literal-negative var)) watched-literals unused-vars^)))

(define (choose-unused-var unused-vars)
  (define var (set-first unused-vars))
  (values var (set-remove unused-vars var)))

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
  (for/fold ([watched-literals (hash)]
             [unit-literals (set)]
             [found-contradiction #f])
            ([clause (in-formula cnf)]
             [idx (in-naturals)]
             #:break found-contradiction)
      (match clause
        [`(,l1 ,l2 . ,_)
         (let* ([watched-literals
                (hash-update watched-literals
                             (literal-symbol l1)
                             (λ (cls-idx-set) (set-add cls-idx-set idx))
                             (λ () (set idx)))]
                [watched-literals
                 (hash-update watched-literals
                              (literal-symbol l2)
                              (λ (cls-idx-set) (set-add cls-idx-set idx))
                              (λ () (set idx)))])
           (values watched-literals unit-literals #f))]
        [`(,l1)
         (values watched-literals (set-add unit-literals l1)
                 (set-member? unit-literals (negate-literal l1)))]
        ['() (values watched-literals unit-literals #f)])))


(define (literal-value lit assignment)
  (for/fold ([value 'undefined])
            ([assigned-lit (in-list assignment)]
             #:final (equal? (literal-symbol assigned-lit)
                             (literal-symbol lit)))
    (literal-phase assigned-lit)))
(module+ test
  (require rackunit)
  (check-equal?  (literal-value (literal 'x #t) '()) 'undefined)
  (check-equal?  (literal-value (literal 'x #t) (list (literal 'x #t))) #t)
  (check-equal?  (literal-value (literal 'x #t) (list (literal 'x #f))) #f)
  )
