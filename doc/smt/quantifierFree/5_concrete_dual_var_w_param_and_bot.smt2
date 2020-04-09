; Id < Exp < Exps
; X:Exps /\ S:Stmt /\ ((X:Exp /\ S:Exps) \/ (X:Id /\ S:Stmt))
; constraints predicate: rule var X; S => (X, S)
; r - rewrite, p - parens

(set-logic QF_DT)
;(set-info :status sat)
(set-option :produce-models true)
(declare-datatypes ((Sort 0))
   (((Id) (Exp) (Exps) (Stmt) (Unused) (Bot))))

; subsorts POSet
(define-fun <Sort ((x Sort) (y Sort)) Bool
   (or (and (= x Bot) (= y Id))
       (and (= x Bot) (= y Exp))
       (and (= x Bot) (= y Exps))
       (and (= x Bot) (= y Stmt))
       (and (= x Id) (= y Exp))
       (and (= x Id) (= y Exps))
       (and (= x Exp) (= y Exps))))
(define-fun <=Sort ((x Sort) (y Sort)) Bool
   (or (= x y) (<Sort x y)))

(declare-const x Sort)
(declare-const s Sort)
(declare-const r Sort)
(declare-const p Sort)

(define-fun constraints () Bool
    (and (<=Sort x Exps)
         (<=Sort s Stmt)
         (<=Sort Stmt r) ; left
         (or (and (<=Sort p r)
                  (<=Sort Exps p)
                  (<=Sort x Exp)
                  (<=Sort s Exps))
             (and (<=Sort Stmt r)
                  (<=Sort x Id)
                  (<=Sort s Stmt)))))

(assert constraints)

(assert-soft (= Unused x)  :id A)
(assert-soft (= Unused s)  :id A)
(assert-soft (= Unused r)  :id A)
(assert-soft (= Unused p)  :id A)

(assert-soft (= Bot x)  :id A :weight -1) ; not really needed, but helps getting a valid first solution
(assert-soft (= Bot s)  :id A :weight -1)
(assert-soft (= Bot r)  :id A :weight -1)
(assert-soft (= Bot p)  :id A :weight -1)


(check-sat)
(get-model)
; Assert not to give the current solution and any other solution subsorted to the current one.
; Supersorted or uncomparable are ok. This makes it reach the final solutions much faster.
; Parameters should not be minimized here since it might restrict variables.
(assert (and (not (and (= x Id) (= s Stmt) (= r Stmt)))
                 (not (<Sort x Id)) (not (<Sort s Stmt))))

(set-info :status unsat)
(check-sat)
