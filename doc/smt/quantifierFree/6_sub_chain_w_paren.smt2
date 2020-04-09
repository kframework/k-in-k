; A < B < C < D
; syntax {S} S ::= "(" S ")"
; (X:C)

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
       (and (= x B) (= y C))
       (and (= x B) (= y D))
       (and (= x C) (= y D))))
(define-fun <=Sort ((x Sort) (y Sort)) Bool
   (or (= x y) (<Sort x y)))

; variables and parameters
(declare-const x Sort)
(declare-const p Sort)

; constraints predicate
(define-fun constraints () Bool
    (and  (<=Sort x C)
          (<=Sort x p)
          (<=Sort p D)))

(assert constraints)

(assert-soft (= Unused x)  :id A)
(assert-soft (= Unused p)  :id A)

(assert-soft (= Bot x)  :id A :weight -1) ; not really needed, but helps getting a valid first solution

; Assert not to give the current solution and any other solution subsorted to the current one.
; Supersorted or uncomparable are ok. This makes it reach the final solutions much faster.
; Parameters should not be minimized here since it might restrict variables.
(assert (and (not (and (= x B) (= B p)))
              (not (<Sort x B))))
(assert (and (not (and (= x C) (= C p)))
              (not (<Sort x C))))
(assert (and (not (and (= x C) (= D p)))
              (not (<Sort x C))))

(check-sat)
(get-model)
