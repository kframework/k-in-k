; Id < Exp < Exps
; X:Exps /\ S:Stmt /\ ((X:Exp /\ S:Exps) \/ (X:Id /\ S:Stmt))
; constraints predicate: rule var X; S => (X, S)

(set-logic ALL)
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

(define-fun constraints ((x Sort) (s Sort)) Bool
    (and (<=Sort x Exps)
         (<=Sort s Stmt)
         (or (and (<=Sort x Exp)
                  (<=Sort s Exps))
             (and (<=Sort x Id)
                  (<=Sort s Stmt)))))

(assert (constraints x s))

; maximality
(assert (not (exists ((xp Sort) (sp Sort))
            (and (constraints xp sp)
                 (or (<Sort x xp)
                     (<Sort s sp))))))

(check-sat)
(get-model)
(assert (not (and (= x Id) (= s Stmt))))

(set-info :status unsat)
(check-sat)
