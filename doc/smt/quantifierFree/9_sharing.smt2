; test sharing
; sorts: A < B < C
; syntax {R} R ::= R "=>" R
; syntax {R} R ::= "(" R ")"
; syntax B ::= B "+" B | B "*" B
; <k> X => (Y + Z) * Q </k> <env> X:A </env>

(set-logic QF_DT)
(set-info :status sat)
(set-option :produce-models true)
(declare-datatypes ((Sort 0))
   (((A) (B) (C) (Unused))))

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
(define-fun constraints2 () Bool
    (and (<=Sort y B)
         (<=Sort z B)
         (<=Sort B p)))

(define-fun constraints () Bool
    (and (or ; rewrite at the top
             (and (<=Sort x r1) ; LHS
                  (<=Sort B r1) ; RHS
                  (<=Sort p B)
                  constraints2 ; we want to call constraints2 here since it might be missing in some branches
                  (<=Sort q B))
             ; mul at the top
             (and (<=Sort r2 B)
                  (<=Sort x r2) ; LHS
                  (<=Sort p r2) ; RHS
                  constraints2
                  (<=Sort q B))
         )
         (<=Sort x A)))

(assert constraints)

(assert-soft (= Unused x)  :id A)
(assert-soft (= Unused y)  :id A)
(assert-soft (= Unused z)  :id A)
(assert-soft (= Unused q)  :id A)
(assert-soft (= Unused r1) :id A)
(assert-soft (= Unused r2) :id A)
(assert-soft (= Unused p)  :id A)


; Assert not to give the current solution and any other solution subsorted to the current one.
; Supersorted or uncomparable are ok. This makes it reach the final solutions much faster.
; Parameters should not be minimized here since it might restrict variables.
(assert (and (not (and (= x A)            (= y A)           (= z A)           (= q A)           (= B r1)           (= B p)))
              (not (<Sort x A))  (not (<Sort y A)) (not (<Sort z A)) (not (<Sort q A)) ))
(assert (and (not (and (= x A)            (= y B)           (= z A)           (= q B)           (= B r2)           (= B p)))
              (not (<Sort x A))  (not (<Sort y B)) (not (<Sort z A)) (not (<Sort q B)) ))
(assert (and (not (and (= x A)            (= y B)           (= z B)           (= q B)           (= B r2)           (= B p))) ; sol 1
              (not (<Sort x A))  (not (<Sort y B)) (not (<Sort z B)) (not (<Sort q B)) ))
(assert (and (not (and (= x A)            (= y B)           (= z B)           (= q B)           (= B r1)           (= B p))) ; sol 2
              (not (<Sort x A))  (not (<Sort y B)) (not (<Sort z B)) (not (<Sort q B)) ))
(assert (and (not (and (= x A)            (= y B)           (= z B)           (= q B)           (= C r1)           (= B p)))
              (not (<Sort x A))  (not (<Sort y B)) (not (<Sort z B)) (not (<Sort q B)) ))

(check-sat)
(get-model)
