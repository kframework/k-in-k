; test sharing
; sorts: A < B
; syntax {S} B ::= "(" S ")" [klabel(r1)]
; syntax {S} B ::= "(" S ")" [klabel(r2)]
; syntax B ::= "x"
; parse: <k> (x) <k>

(set-logic ALL)
(set-info :status sat)
(set-option :produce-models true)
(declare-datatypes ((Sort 0))
   (((A) (B))))

; subsorts POSet
(define-fun <Sort ((x Sort) (y Sort)) Bool
   (or (and (= x A) (= y B))))
(define-fun <=Sort ((x Sort) (y Sort)) Bool
   (or (= x y) (<Sort x y)))

(declare-const r1 Sort)
(declare-const r2 Sort)

; constraints predicate
(define-fun constraints ((r1 Sort) (r2 Sort)) Bool
    (and (or (and (<=Sort B r1))
             (and (<=Sort B r2))
         )))

(assert (constraints r1 r2))

; maximality for vars and min for parameters
(assert (not (exists ((r1p Sort) (r2p Sort))
            (and (constraints r1p r2p)
                 (ite (not (and true))  ; if variables not maximized
                      (or true) ; check variables maximality
                      (or (<Sort r1p r1) (<Sort r2p r2)) ; check param minimality
                     )))))

;(assert (not (and (= r1 A) (= r2 B))))
;(assert (not (and (= r1 B) (= r2 A))))
; these are the expected solutions but 'check param minimality' is never false
; because each solution is compared with the other one

(check-sat)
(get-model)
