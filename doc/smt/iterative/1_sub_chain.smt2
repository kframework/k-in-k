; A < B < C < D
; X:C

(set-logic ALL)
(set-option :produce-models true)
(declare-datatypes ((Sort 0))
   (((A) (B) (C) (D))))

; subsorts POSet
(define-fun <Sort ((x Sort) (y Sort)) Bool
   (or (and (= x A) (= y B))
       (and (= x A) (= y C))
       (and (= x A) (= y D))
       (and (= x B) (= y C))
       (and (= x B) (= y D))
       (and (= x C) (= y D))))
(define-fun <=Sort ((x Sort) (y Sort)) Bool
   (or (= x y) (<Sort x y)))

; variables and parameters
(declare-const x Sort)

; constraints predicate
(define-fun constraints ((x Sort)) Bool
    (and  (<=Sort x C)))

(assert (constraints x))

; maximality for vars and min for parameters
(assert (not (exists ((xp Sort))
            (and (constraints xp)
                 (<Sort x xp)))))

(check-sat)
(get-model)
(assert (not (= x C)))

(set-info :status unsat)
(check-sat)
