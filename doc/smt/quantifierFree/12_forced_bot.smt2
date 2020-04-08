; Bot < A B < C
; X:A /\ X:B

(set-logic QF_DT)
(set-option :produce-models true)
(declare-datatypes ((Sort 0))
   (((A) (B) (C) (Unused) (Bot))))

; subsorts POSet
(define-fun <Sort ((x Sort) (y Sort)) Bool
   (or (and (= x Bot) (= y A))
       (and (= x Bot) (= y B))
       (and (= x Bot) (= y C))
       (and (= x A) (= y C))
       (and (= x B) (= y C))))
(define-fun <=Sort ((x Sort) (y Sort)) Bool
   (or (= x y) (<Sort x y)))

; variables and parameters
(declare-const x Sort)

; constraints predicate
(define-fun constraints () Bool
    (and  (<=Sort x A)
          (<=Sort x B)))

(assert constraints)

(assert-soft (= Unused x)  :id A)

(assert-soft (= Bot x)  :id A :weight -1) ; not really needed, but helps getting a valid first solution

(check-sat)
(get-model)
(assert (not (= x Bot)))

(set-info :status unsat)
(check-sat)
