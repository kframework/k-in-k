; A < B C < D
; X:B \/ X:C

(set-logic QF_DT)
(set-info :status sat)
(set-option :produce-models true)
(declare-datatypes ((Sort 0))
   (((A) (B) (C) (D) (Unused) (Bot))))

; subsorts POSet
(define-fun <Sort ((x Sort) (y Sort)) Bool
   (or (and (= x Bot) (= y A))
       (and (= x Bot) (= y B))
       (and (= x Bot) (= y C))
       (and (= x Bot) (= y D))
       (and (= x A) (= y B))
       (and (= x A) (= y C))
       (and (= x A) (= y D))
       (and (= x B) (= y D))
       (and (= x C) (= y D))))
(define-fun <=Sort ((x Sort) (y Sort)) Bool
   (or (= x y) (<Sort x y)))

; variables and parameters
(declare-const x Sort)

; constraints predicate
(define-fun constraints () Bool
    (or (<=Sort x B)
        (<=Sort x C)))

(assert constraints)

(assert-soft (= Unused x)  :id A)

(assert-soft (= Bot x)  :id A :weight -1) ; not really needed, but helps getting a valid first solution


(check-sat)
(get-model)
(assert (and (not (= x A)) (not (<=Sort x A)))) ; assert not to give the current solution and any other solution subsorted to the current one
(assert (and (not (= x C)) (not (<=Sort x C)))) ; supersorted or uncomparable are ok
(assert (and (not (= x B)) (not (<=Sort x B))))

(set-info :status unsat)
(check-sat)
