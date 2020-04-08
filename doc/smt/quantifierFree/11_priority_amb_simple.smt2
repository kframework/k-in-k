; test sharing
; sorts: A < B
; syntax {S} B ::= "(" S ")" [klabel(r1)]
; syntax {S} B ::= "(" S ")" [klabel(r2)]
; syntax B ::= "x"
; parse: <k> (x) <k>

(set-logic QF_DT)
(set-info :status sat)
(set-option :produce-models true)
(declare-datatypes ((Sort 0))
   (((A) (B) (Unused))))

; subsorts POSet
(define-fun <Sort ((x Sort) (y Sort)) Bool
   (or (and (= x A) (= y B))))
(define-fun <=Sort ((x Sort) (y Sort)) Bool
   (or (= x y) (<Sort x y)))

(declare-const r1 Sort)
(declare-const r2 Sort)

; constraints predicate
(define-fun constraints () Bool
    (and (or (and (<=Sort B r1))
             (and (<=Sort B r2))
         )))

(assert constraints)

(assert-soft (= Unused r1) :id A)
(assert-soft (= Unused r2) :id A)


(check-sat)
(get-model)

(assert (not (= r2 B)))
(check-sat)
(get-model)

(assert (not (= r1 B)))
(set-info :status unsat)
(check-sat)
