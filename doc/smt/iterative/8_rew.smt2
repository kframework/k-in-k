; test for greatest lower bound in parametric production
; sorts: A B < C < D
; syntax {R} R ::= R "=>" R
; X:A => Y:B

(set-logic ALL)
(set-info :status sat)
(set-option :produce-models true)
(declare-datatypes ((Sort 0))
   (((A) (B) (C) (D))))

; subsorts POSet
(define-fun <Sort ((x Sort) (y Sort)) Bool
   (or (and (= x A) (= y C))
       (and (= x A) (= y D))
       (and (= x B) (= y C))
       (and (= x B) (= y D))
       (and (= x C) (= y D))))
(define-fun <=Sort ((x Sort) (y Sort)) Bool
   (or (= x y) (<Sort x y)))

(declare-const x Sort)
(declare-const y Sort)
(declare-const r Sort)

; constraints predicate
(define-fun constraints ((x Sort) (y Sort) (r Sort)) Bool
    (and  (<=Sort x A)
          (<=Sort y B)
          (<=Sort x r)
          (<=Sort y r)))

(assert (constraints x y r))

; maximality for vars and min for parameters
(assert (not (exists ((xp Sort) (yp Sort) (rp Sort))
            (and (constraints xp yp rp)
                 (ite (not (and (= x xp) (= y yp)))  ; if variables not maximized
                      (or (<Sort x xp) (<Sort y yp)) ; check variables maximality
                      (or (<Sort rp r)) ; check param minimality
                     )))))

(check-sat)
(get-model)
(assert (not (and (= x A) (= y B) (= r C))))

(set-info :status unsat)
(check-sat)
