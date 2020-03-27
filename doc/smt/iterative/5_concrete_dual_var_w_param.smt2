; Id < Exp < Exps
; X:Exps /\ S:Stmt /\ ((X:Exp /\ S:Exps) \/ (X:Id /\ S:Stmt))
; constraints predicate: rule var X; S => (X, S)
; r - rewrite, p - parens

(set-logic ALL)
;(set-info :status sat)
(set-option :produce-models true)
(declare-datatypes ((Sort 0))
   (((Id) (Exp) (Exps) (Stmt))))

; subsorts POSet
(define-fun <Sort ((x Sort) (y Sort)) Bool
   (or (and (= x Id) (= y Exp))
       (and (= x Id) (= y Exps))
       (and (= x Exp) (= y Exps))))
(define-fun <=Sort ((x Sort) (y Sort)) Bool
   (or (= x y) (<Sort x y)))

(declare-const x Sort)
(declare-const s Sort)
(declare-const r Sort)
(declare-const p Sort)

(define-fun constraints ((x Sort) (s Sort) (r Sort) (p Sort)) Bool
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

(assert (constraints x s r p))

; maximality
(assert (not (exists ((xp Sort) (sp Sort) (rp Sort) (pp Sort))
            (and (constraints xp sp rp pp)
                 (ite (not (and (= x xp) (= s sp)))
                     (or (<Sort x xp) (<Sort s sp))
                     (or (<Sort rp r) (<Sort pp p))
                     )))))

; 2 solutions because we don't have a bottom sort
(check-sat)
(get-model)
(assert (not (and (= x Id) (= s Stmt) (= r Stmt) (= p Id))))

(check-sat)
(get-model)
(assert (not (and (= x Id) (= s Stmt) (= r Stmt) (= p Stmt))))

(set-info :status unsat)
(check-sat)
