; Id < Exp < Exps
; X:Exps /\ S:Stmt /\ ((X:Exp /\ S:Exps) \/ (X:Id /\ S:Stmt))

(set-logic ALL)
(set-info :status sat)
; use finite model finding heuristic for quantifier instantiation
(set-option :finite-model-find true)
(set-option :produce-models true)
(declare-datatypes ((Sort 0))
   (((Id) (Exp) (Exps) (Stmt))))

; subsorts POSet
(define-fun tsubs () (Set (Tuple Sort Sort))
    (tclosure (insert ; initial subsorts
        (mkTuple Id Exp) (singleton
        (mkTuple Exp Exps)))))

(define-fun <Sort ((x Sort) (y Sort)) Bool
   (member (mkTuple x y) tsubs))
(define-fun <=Sort ((x Sort) (y Sort)) Bool
   (or (= x y) (<Sort x y)))

; constraints predicate: rule var X; S => (X, S)
(define-fun constraints ((x Sort) (s Sort)) Bool
    (and (<=Sort x Exps)
         (<=Sort s Stmt)
         (or (and (<=Sort x Exp)
                  (<=Sort s Exps))
             (and (<=Sort x Id)
                  (<=Sort s Stmt)))))

; maximality
(define-fun maximality ((x Sort) (s Sort)) Bool
    (not (exists ((xp Sort) (sp Sort))
                (and (constraints xp sp)
                     (or (<Sort x xp)
                         (<Sort s sp))))))

(define-fun isSol ((x (Tuple Sort Sort))) Bool
    (and (constraints ((_ tupSel 0) x) ((_ tupSel 1) x))
         (maximality  ((_ tupSel 0) x) ((_ tupSel 1) x))))

; solution to be found
(declare-fun solSet () (Set (Tuple Sort Sort)))

; completeness
(assert (forall ((x (Tuple Sort Sort)))
              (and (=> (isSol x) (member x solSet))
                   (=> (member x solSet) (isSol x)))))

(check-sat)
(get-model)

; SOLUTION: (define-fun solSet () (Set (Tuple Sort Sort)) (singleton (mkTuple Id Stmt)))
