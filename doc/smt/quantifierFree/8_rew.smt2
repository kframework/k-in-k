; test for greatest lower bound in parametric production
; sorts: A B < C < D
; syntax {R} R ::= R "=>" R
; X:A => Y:B

(set-logic QF_DT)
(set-info :status sat)
(set-option :produce-models true)
(declare-datatypes ((Sort 0))
   (((A) (B) (C) (D) (Unused))))

; subsorts POSet
(define-fun <Sort ((x Sort) (y Sort)) Bool
   (or (and (= x A) (= y C))
       (and (= x A) (= y D))
       (and (= x B) (= y C))
       (and (= x B) (= y D))
       (and (= x C) (= y D))))
(define-fun <=Sort ((x Sort) (y Sort)) Bool
   (or (= x y) (<Sort x y)))

(declare-const x Sort)
(declare-const y Sort)
(declare-const r Sort)

; constraints predicate
(define-fun constraints () Bool
    (and  (<=Sort x A)
          (<=Sort y B)
          (<=Sort x r)
          (<=Sort y r)))

(assert constraints)

(assert-soft (= Unused x)  :id A)
(assert-soft (= Unused y)  :id A)
(assert-soft (= Unused r)  :id A)


(check-sat)
(get-model)

(assert (not (and (= x A) (= y B) (= r D))))
(check-sat)
(get-model)

(assert (not (and (= x A) (= y B) (= r C))))
(set-info :status unsat)
(check-sat)
