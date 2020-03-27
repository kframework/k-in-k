; A < B < C < D
; syntax {S} S ::= "(" S ")"
; (X:C)

(set-logic ALL)
(set-info :status sat)
; use finite model finding heuristic for quantifier instantiation
(set-option :finite-model-find true)
(set-option :produce-models true)
(declare-datatypes ((Sort 0))
   (((A) (B) (C) (D))))

; subsorts POSet
(define-fun tsubs () (Set (Tuple Sort Sort))
    (tclosure (insert ; initial subsorts
        (mkTuple A B)
        (mkTuple B C) (singleton
        (mkTuple C D)))))

(define-fun <Sort ((x Sort) (y Sort)) Bool
   (member (mkTuple x y) tsubs))
(define-fun <=Sort ((x Sort) (y Sort)) Bool
   (or (= x y) (<Sort x y)))

; constraints predicate
(define-fun constraints ((x Sort) (p Sort)) Bool
    (and  (<=Sort x C)
          (<=Sort x p)
          (<=Sort p D)))

; maximality for vars and min for parameters
(define-fun maximality ((x Sort) (p Sort)) Bool
    (not (exists ((xp Sort) (pp Sort))
                (and (constraints xp pp)
                     (ite (not (= x xp))
                          (<Sort x xp)
                          (<Sort pp p)
                         )))))

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

; SOLUTION: (define-fun solSet () (Set (Tuple Sort Sort)) (singleton (mkTuple C C)))
