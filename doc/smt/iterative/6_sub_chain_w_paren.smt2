; A < B < C < D
; syntax {S} S ::= "(" S ")"
; (X:C)

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

(declare-const x Sort)
(declare-const p Sort)

; constraints predicate
(define-fun constraints ((x Sort) (p Sort)) Bool
    (and  (<=Sort x C)
          (<=Sort x p)
          (<=Sort p D)))

(assert (constraints x p))

; maximality for vars and min for parameters
(assert (not (exists ((xp Sort) (pp Sort))
            (and (constraints xp pp)
                 (ite (not (= x xp))
                      (<Sort x xp)
                      (<Sort pp p))))))

(check-sat)
(get-model)
(assert (not (and (= x C) (= p C))))

(set-info :status unsat)
(check-sat)
