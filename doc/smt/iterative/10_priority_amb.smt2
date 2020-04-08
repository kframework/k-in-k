; test sharing
; sorts: A < B
; syntax {R} R ::= R "=>" R
; syntax {R} R ::= "(" R ")"
; syntax B ::= B "+" B | B "*" B
; <k> X => Y * Z </k>

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

(declare-const x Sort)
(declare-const y Sort)
(declare-const z Sort)
(declare-const r1 Sort)
(declare-const r2 Sort)

; constraints predicate
(define-fun constraints ((x Sort) (y Sort) (z Sort) (r1 Sort) (r2 Sort)) Bool
    (and (or ; rewrite at the top
             (and (<=Sort x r1) ; LHS
                  (<=Sort B r1) ; RHS
                  (<=Sort y B)
                  (<=Sort z B)
                  )
             ; mul at the top
             (and (<=Sort r2 B)
                  (<=Sort x r2) ; LHS
                  (<=Sort y r2) ; RHS
                  (<=Sort z B)
                  )
         )))

(assert (constraints x y z r1 r2))

; maximality for vars and min for parameters
(assert (not (exists ((xp Sort) (yp Sort) (zp Sort) (r1p Sort) (r2p Sort)) ; TODO: maybe move parameters in the else branch?
            (and (constraints xp yp zp r1p r2p)
                 (ite (not (and (= x xp) (= y yp) (= z zp)))  ; if variables not maximized
                      (or (<Sort x xp) (<Sort y yp) (<Sort z zp)) ; check variables maximality
                      (or (<Sort r1p r1) (<Sort r2p r2)) ; check param minimality
                     )))))

;(assert (not (and (= x B) (= y B) (= z B) (= r1 B) (= r2 A)))) ; sol 1: rew at the top, r2 not used so minimized to A
;(assert (not (and (= x B) (= y B) (= z B) (= r1 A) (= r2 B)))) ; sol 2: mul at the top, r1 not used so minimized to A
; these are the expected solutions but 'check param minimality' is never false
; because each solution is compared with the other one


(check-sat)
(get-model)
