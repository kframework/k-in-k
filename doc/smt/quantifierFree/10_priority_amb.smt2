; test sharing
; sorts: A < B
; syntax {R} R ::= R "=>" R
; syntax {R} R ::= "(" R ")"
; syntax B ::= B "+" B | B "*" B
; <k> X => Y * Z </k>

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

(declare-const x Sort)
(declare-const y Sort)
(declare-const z Sort)
(declare-const r1 Sort)
(declare-const r2 Sort)

; constraints predicate
(define-fun constraints () Bool
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

(assert constraints)

(assert-soft (= Unused x)  :id A)
(assert-soft (= Unused y)  :id A)
(assert-soft (= Unused z)  :id A)
(assert-soft (= Unused r1) :id A)
(assert-soft (= Unused r2) :id A)


; all possible solutions
;(assert (not (and (= x A) (= y A) (= z A) (= r2 A))))
;(assert (not (and (= x A) (= y A) (= z B) (= r2 A))))
;(assert (not (and (= x A) (= y A) (= z A) (= r2 B))))
;(assert (not (and (= x A) (= y B) (= z A) (= r2 B))))1
;(assert (not (and (= x A) (= y B) (= z B) (= r2 B))))
;(assert (not (and (= x A) (= y A) (= z B) (= r2 B))))
;(assert (not (and (= x B) (= y A) (= z A) (= r2 B))))
;(assert (not (and (= x B) (= y B) (= z A) (= r2 B))))
;(assert (not (and (= x B) (= y A) (= z B) (= r2 B))))
;(assert (not (and (= x B) (= y B) (= z B) (= r2 B))))

;(assert (not (and (= r1 B) (= x A) (= y A) (= z A))))
;(assert (not (and (= r1 B) (= x B) (= y A) (= z A))))
;(assert (not (and (= r1 B) (= x B) (= y B) (= z A))))
;(assert (not (and (= r1 B) (= x A) (= y B) (= z A))))
;(assert (not (and (= r1 B) (= x A) (= y A) (= z B))))
;(assert (not (and (= r1 B) (= x A) (= y B) (= z B))))
;(assert (not (and (= r1 B) (= x B) (= y A) (= z B))))
;(assert (not (and (= r1 B) (= x B) (= y B) (= z B))))

; Assert not to give the current solution and any other solution subsorted to the current one.
; Supersorted or uncomparable are ok. This makes it reach the final solutions much faster.
; Parameters should not be minimized here since it might restrict variables.
(assert (and (not (and (= x A)           (= y A)           (= z A)           (= A r2)))
              (not (<Sort x A)) (not (<Sort y A)) (not (<Sort z A))                  ))
(assert (and (not (and (= x A)           (= y A)           (= z B)           (= A r2)))
              (not (<Sort x A)) (not (<Sort y A)) (not (<Sort z B))                  ))
(assert (and (not (and (= x B)           (= y B)           (= z B)           (= B r2))) ; maximal sol 1
              (not (<Sort x B)) (not (<Sort y B)) (not (<Sort z B))                  ))
(assert (and (not (and (= x B)           (= y B)           (= z B)           (= B r1))) ; maximal sol 2
              (not (<Sort x B)) (not (<Sort y B)) (not (<Sort z B))                  ))
(check-sat)
(get-model)

(set-info :status unsat)
(check-sat)
