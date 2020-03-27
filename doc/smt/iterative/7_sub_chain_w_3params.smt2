; A < B < C < D
; syntax {R, P, Q} R ::= [ P, Q ]
; [ X , Y ] /\ Y:B

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
(declare-const y Sort)
(declare-const r Sort)
(declare-const p Sort)
(declare-const q Sort)

; constraints predicate
(define-fun constraints ((x Sort) (y Sort) (r Sort) (p Sort) (q Sort)) Bool
    (and  (<=Sort x p)
          (<=Sort y q)
          (<=Sort y B)))

(assert (constraints x y r p q))

; maximality for vars and min for parameters
(assert (not (exists ((xp Sort) (yp Sort) (rp Sort) (pp Sort) (qp Sort))
            (and (constraints xp yp rp pp qp)
                 (ite (not (and (= x xp) (= y yp)))  ; if variables not maximized
                      (or (<Sort x xp) (<Sort y yp)) ; check variables maximality
                      (or (<Sort rp r) (<Sort pp p) (<Sort qp q)) ; check param minimality
                     )))))

(check-sat)
(get-model)
(assert (not (and (= x D) (= y B) (= r A) (= p D) (= q B))))

(set-info :status unsat)
(check-sat)
