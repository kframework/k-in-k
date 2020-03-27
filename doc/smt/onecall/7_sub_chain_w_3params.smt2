; A < B < C < D
; syntax {R, P, Q} R ::= [ P, Q ]
; [ X , Y ] /\ Y:B

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
(define-fun constraints ((x Sort) (y Sort) (r Sort) (p Sort) (q Sort)) Bool
    (and  (<=Sort x p)
          (<=Sort y q)
          (<=Sort y B)))

; maximality for vars and min for parameters
(define-fun maximality ((x Sort) (y Sort) (r Sort) (p Sort) (q Sort)) Bool
    (not (exists ((xp Sort) (yp Sort) (rp Sort) (pp Sort) (qp Sort))
                (and (constraints xp yp rp pp qp)
                     (ite (not (and (= x xp) (= y yp)))
                          (or (<Sort x xp) (<Sort y yp))
                          (or (<Sort rp r) (<Sort pp p) (<Sort qp q))
                         )))))

(define-fun isSol ((sol (Tuple Sort Sort Sort Sort Sort))) Bool
    (and (constraints ((_ tupSel 0) sol) ((_ tupSel 1) sol) ((_ tupSel 2) sol) ((_ tupSel 3) sol) ((_ tupSel 4) sol))
         (maximality  ((_ tupSel 0) sol) ((_ tupSel 1) sol) ((_ tupSel 2) sol) ((_ tupSel 3) sol) ((_ tupSel 4) sol))
         ))

; solution to be found
(declare-fun solSet () (Set (Tuple Sort Sort Sort Sort Sort)))

; completeness
(assert (forall ((sol (Tuple Sort Sort Sort Sort Sort)))
              (and (=> (isSol sol) (member sol solSet))
                   (=> (member sol solSet) (isSol sol)))))

; TEST: single maximal solution
;(declare-const sol (Tuple Sort Sort Sort Sort Sort))
;(assert (isSol sol))
;(assert (not (= sol (mkTuple D B A D B))))


(check-sat)
(get-model)

; SOLUTION: (define-fun solSet () (Set (Tuple Sort Sort Sort Sort Sort)) (singleton (mkTuple D B A D B))) ; around 1 minute with cvc4-1.6 (1.7 onwards is a lot slower)
