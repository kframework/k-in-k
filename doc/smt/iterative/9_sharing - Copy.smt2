; test sharing
; sorts: A < B < C
; syntax {R} R ::= R "=>" R
; syntax {R} R ::= "(" R ")"
; syntax B ::= B "+" B | B "*" B
; <k> X => (Y + Z) * Q </k> <env> X:A </env>
; <k> X => (Y)     * Q </k> <env> X:A </env> ; can we do sharing here? Because the path is not common. Yes, we must reference the inner relation in the constraint

(set-logic ALL)
(set-info :status sat)
(set-option :produce-models true)
(declare-datatypes ((Sort 0))
   (((A) (B) (C))))

; subsorts POSet
(define-fun <Sort ((x Sort) (y Sort)) Bool
   (or (and (= x A) (= y B))
       (and (= x A) (= y C))
       (and (= x B) (= y C))))
(define-fun <=Sort ((x Sort) (y Sort)) Bool
   (or (= x y) (<Sort x y)))

(declare-const x Sort)
(declare-const y Sort)
(declare-const z Sort)
(declare-const q Sort)
(declare-const r1 Sort)
(declare-const r2 Sort)
(declare-const p Sort)

; constraints predicate
(define-fun constraints2 ((x Sort) (y Sort) (z Sort) (q Sort) (r1 Sort) (r2 Sort) (p Sort)) Bool ; is it bad if we leave all parameters?
    (and (<=Sort y B)
         (<=Sort z B)
         (<=Sort B p)))

(define-fun constraints ((x Sort) (y Sort) (z Sort) (q Sort) (r1 Sort) (r2 Sort) (p Sort)) Bool
    (and (or ; rewrite at the top
             (and (<=Sort x r1) ; LHS
                  (<=Sort B r1) ; RHS
                  (<=Sort p B)
                  (constraints2 x y z q r1 r2 p) ; we want to call constraints2 here since it might be missing in some branches
                  (<=Sort q B))
             ; mul at the top
             (and (<=Sort r2 B)
                  (<=Sort x r2) ; LHS
                  (<=Sort p r2) ; RHS
                  (constraints2 x y z q r1 r2 p)
                  (<=Sort q B))
         )
         (<=Sort x A)))


(assert (constraints x y z q r1 r2 p))

; maximality for vars and min for parameters
(assert (not (exists ((xp Sort) (yp Sort) (zp Sort) (qp Sort) (r1p Sort) (r2p Sort) (pp Sort)) ; TODO: maybe move parameters in the else branch?
            (and (constraints xp yp zp qp r1p r2p pp)
                 (ite (not (and (= x xp) (= y yp) (= z zp) (= q qp)))  ; if variables not maximized
                      (or (<Sort x xp) (<Sort y yp) (<Sort z zp) (<Sort q qp)) ; check variables maximality
                      (or (<Sort r1p r1) (<Sort r2p r2) (<Sort pp p)) ; check param minimality
                     )))))
;(assert (= y B))
;(assert (= z B))
;(assert (= q B))

;(check-sat)
;(get-model)
;(assert (not (and (= x A) (= y B) (= z B) (= q B) (= r1 A) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y B) (= z A) (= q B) (= r1 A) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y A) (= z B) (= q B) (= r1 A) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y A) (= z A) (= q B) (= r1 A) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y B) (= z B) (= q A) (= r1 A) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y B) (= z A) (= q A) (= r1 A) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y A) (= z B) (= q A) (= r1 A) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y A) (= z A) (= q A) (= r1 A) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y B) (= z B) (= q B) (= r1 B) (= r2 A) (= p B))))
;(assert (not (and (= x A) (= y B) (= z B) (= q B) (= r1 B) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y B) (= z B) (= q B) (= r1 B) (= r2 C) (= p B)))) ; sol 1: rewrite at the top
;(assert (not (and (= x A) (= y B) (= z B) (= q B) (= r1 B) (= r2 A) (= p B))))
;(assert (not (and (= x A) (= y B) (= z A) (= q B) (= r1 B) (= r2 A) (= p B))))
;(assert (not (and (= x A) (= y B) (= z A) (= q B) (= r1 B) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y B) (= z A) (= q B) (= r1 B) (= r2 C) (= p B))))
;(assert (not (and (= x A) (= y B) (= z A) (= q B) (= r1 B) (= r2 C) (= p B))))
;(assert (not (and (= x A) (= y A) (= z B) (= q B) (= r1 B) (= r2 A) (= p B))))
;(assert (not (and (= x A) (= y A) (= z B) (= q B) (= r1 B) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y A) (= z B) (= q B) (= r1 B) (= r2 C) (= p B))))
;(assert (not (and (= x A) (= y A) (= z A) (= q B) (= r1 B) (= r2 A) (= p B))))
;(assert (not (and (= x A) (= y A) (= z A) (= q B) (= r1 B) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y A) (= z A) (= q B) (= r1 B) (= r2 C) (= p B))))
;(assert (not (and (= x A) (= y B) (= z B) (= q A) (= r1 B) (= r2 A) (= p B))))
;(assert (not (and (= x A) (= y B) (= z B) (= q A) (= r1 B) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y B) (= z B) (= q A) (= r1 B) (= r2 C) (= p B))))
;(assert (not (and (= x A) (= y B) (= z A) (= q A) (= r1 B) (= r2 A) (= p B))))
;(assert (not (and (= x A) (= y B) (= z A) (= q A) (= r1 B) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y B) (= z A) (= q A) (= r1 B) (= r2 C) (= p B))))
;(assert (not (and (= x A) (= y A) (= z B) (= q A) (= r1 B) (= r2 A) (= p B))))
;(assert (not (and (= x A) (= y A) (= z B) (= q A) (= r1 B) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y A) (= z B) (= q A) (= r1 B) (= r2 C) (= p B))))
;(assert (not (and (= x A) (= y A) (= z A) (= q A) (= r1 B) (= r2 A) (= p B))))
;(assert (not (and (= x A) (= y A) (= z A) (= q A) (= r1 B) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y A) (= z A) (= q A) (= r1 B) (= r2 C) (= p B))))
;(assert (not (and (= x A) (= y B) (= z B) (= q B) (= r1 C) (= r2 A) (= p B))))
;(assert (not (and (= x A) (= y B) (= z B) (= q B) (= r1 C) (= r2 B) (= p B))))
;(assert (not (and (= x A) (= y B) (= z B) (= q B) (= r1 C) (= r2 C) (= p B))))

(check-sat)
(get-model)



