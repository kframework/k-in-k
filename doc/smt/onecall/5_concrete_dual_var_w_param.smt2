; Id < Exp < Exps
; X:Exps /\ S:Stmt /\ ((X:Exp /\ S:Exps) \/ (X:Id /\ S:Stmt))
; constraints predicate: rule var X; S => (X, S)
; r - rewrite, p - parens

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

; maximality
(define-fun maximality ((x Sort) (s Sort) (r Sort) (p Sort)) Bool
    (not (exists ((xp Sort) (sp Sort) (rp Sort) (pp Sort))
                (and (constraints xp sp rp pp)
                     (ite (not (and (= x xp) (= s sp)))
                         (or (<Sort x xp) (<Sort s sp))
                         (or (<Sort rp r) (<Sort pp p))
                         )))))

(define-fun isSol ((x (Tuple Sort Sort Sort Sort))) Bool
    (and (constraints ((_ tupSel 0) x) ((_ tupSel 1) x) ((_ tupSel 2) x) ((_ tupSel 3) x))
         (maximality  ((_ tupSel 0) x) ((_ tupSel 1) x) ((_ tupSel 2) x) ((_ tupSel 3) x))))

; solution to be found
(declare-fun solSet () (Set (Tuple Sort Sort Sort Sort)))

; completeness
(assert (forall ((x (Tuple Sort Sort Sort Sort)))
              (and (=> (isSol x) (member x solSet))
                   (=> (member x solSet) (isSol x)))))

(check-sat)
(get-model)

; SOLUTION: (define-fun solSet () (Set (Tuple Sort Sort Sort Sort)) (union (singleton (mkTuple Id Stmt Stmt Id)) (singleton (mkTuple Id Stmt Stmt Stmt))))
