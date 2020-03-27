; A < B C < D
; X:B \/ X:C

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
        (mkTuple A C)
        (mkTuple B D) (singleton
        (mkTuple C D)))))

(define-fun <Sort ((x Sort) (y Sort)) Bool
   (member (mkTuple x y) tsubs))
(define-fun <=Sort ((x Sort) (y Sort)) Bool
   (or (= x y) (<Sort x y)))

; constraints predicate
(define-fun constraints ((x Sort)) Bool
    (or  (<=Sort x B)
         (<=Sort x C)))

; maximality
(define-fun maximality ((x Sort)) Bool
    (not (exists ((xp Sort))
                (and (constraints xp)
                     (<Sort x xp)))))

(define-fun isSol ((x (Tuple Sort))) Bool
    (and (constraints ((_ tupSel 0) x))
         (maximality  ((_ tupSel 0) x))))

; solution to be found
(declare-fun solSet () (Set (Tuple Sort)))

; completeness
(assert (forall ((x (Tuple Sort)))
              (and (=> (isSol x) (member x solSet))
                   (=> (member x solSet) (isSol x)))))

(check-sat)
(get-model)

; SOLUTION: (define-fun solSet () (Set (Tuple Sort)) (union (singleton (mkTuple B)) (singleton (mkTuple C))))
