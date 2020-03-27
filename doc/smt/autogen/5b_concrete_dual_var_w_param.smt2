; Id < Exp < Exps
; rule val X ; S => (X, S)
; generated by the Dwight's z3 type inferencer

(set-logic QF_DT)

(declare-datatypes () ((Sort (|SortExps| )
(|SortCell| )
(|SortExp| )
(|SortStmt| )
(|SortKItem| )
(|SortKLabel| )
(|SortId| )
(|SortK| )
(|SortBool| )
(|SortBag| )
)))
(define-fun <=Sort ((s1 Sort) (s2 Sort)) Bool (or
  (and (= s1 |SortKItem|) (= s2 |SortK|))
  (and (= s1 |SortExps|) (= s2 |SortKItem|))
  (and (= s1 |SortExps|) (= s2 |SortK|))
  (and (= s1 |SortBag|) (= s2 |SortKItem|))
  (and (= s1 |SortBag|) (= s2 |SortK|))
  (and (= s1 |SortExp|) (= s2 |SortKItem|))
  (and (= s1 |SortExp|) (= s2 |SortK|))
  (and (= s1 |SortExp|) (= s2 |SortExps|))
  (and (= s1 |SortStmt|) (= s2 |SortKItem|))
  (and (= s1 |SortStmt|) (= s2 |SortK|))
  (and (= s1 |SortBool|) (= s2 |SortKItem|))
  (and (= s1 |SortBool|) (= s2 |SortK|))
  (and (= s1 |SortCell|) (= s2 |SortKItem|))
  (and (= s1 |SortCell|) (= s2 |SortBag|))
  (and (= s1 |SortCell|) (= s2 |SortK|))
  (and (= s1 |SortId|) (= s2 |SortKItem|))
  (and (= s1 |SortId|) (= s2 |SortExp|))
  (and (= s1 |SortId|) (= s2 |SortK|))
  (and (= s1 |SortId|) (= s2 |SortExps|))
  (and (= s1 |SortKItem|) (= s2 |SortKItem|))
  (and (= s1 |SortKLabel|) (= s2 |SortKLabel|))
  (and (= s1 |SortExp|) (= s2 |SortExp|))
  (and (= s1 |SortBag|) (= s2 |SortBag|))
  (and (= s1 |SortId|) (= s2 |SortId|))
  (and (= s1 |SortCell|) (= s2 |SortCell|))
  (and (= s1 |SortBool|) (= s2 |SortBool|))
  (and (= s1 |SortK|) (= s2 |SortK|))
  (and (= s1 |SortStmt|) (= s2 |SortStmt|))
  (and (= s1 |SortExps|) (= s2 |SortExps|))
))
(push)
(declare-const |FreshVarSort_1_1_1_20_#KRewrite| Sort)
(declare-const |VarX| Sort)
(declare-const |VarS| Sort)
(declare-const |FreshVarSort_1_14_1_20| Sort)
(assert (and true (distinct |FreshVarSort_1_1_1_20_#KRewrite| |SortKLabel|) (distinct |FreshVarSort_1_14_1_20| |SortKLabel|) ))
(define-fun |constraint3_SortExps| () Bool                          (and true (<=Sort |VarX|      |SortExps|) ))
(define-fun |constraint5_SortStmt| () Bool                          (and true (<=Sort |VarS|      |SortStmt|) ))
(define-fun |constraint2_FreshVarSort_1_1_1_20_#KRewrite| () Bool   (and true (<=Sort |SortStmt|  |FreshVarSort_1_1_1_20_#KRewrite|) |constraint3_SortExps| |constraint5_SortStmt| ))
(define-fun |constraint8_SortId| () Bool                            (and true (<=Sort |VarX|      |SortId|) ))
(define-fun |constraint10_SortStmt| () Bool                         (and true (<=Sort |VarS|      |SortStmt|) ))
(define-fun |constraint7_FreshVarSort_1_1_1_20_#KRewrite| () Bool   (and true (<=Sort |SortKItem| |FreshVarSort_1_1_1_20_#KRewrite|) |constraint8_SortId| |constraint10_SortStmt| ))
(define-fun |constraint8_SortExp| () Bool                           (and true (<=Sort |VarX|      |SortExp|) ))
(define-fun |constraint10_SortExps| () Bool                         (and true (<=Sort |VarS|      |SortExps|) ))
(define-fun |constraint13_FreshVarSort_1_14_1_20| () Bool           (and true (<=Sort |SortExps|  |FreshVarSort_1_14_1_20|) |constraint8_SortExp| |constraint10_SortExps| ))
(define-fun |constraint12_FreshVarSort_1_1_1_20_#KRewrite| () Bool  (and true (<=Sort |FreshVarSort_1_14_1_20| |FreshVarSort_1_1_1_20_#KRewrite|) |constraint13_FreshVarSort_1_14_1_20| ))
(define-fun amb0 () Bool                                            (or |constraint7_FreshVarSort_1_1_1_20_#KRewrite| |constraint12_FreshVarSort_1_1_1_20_#KRewrite| ))
(define-fun |constraint1_Sort#RuleBody| () Bool                     (and true (<=Sort |FreshVarSort_1_1_1_20_#KRewrite| |SortK|) |constraint2_FreshVarSort_1_1_1_20_#KRewrite| amb0 ))
(define-fun |constraint0_Sort#RuleContent| () Bool                  (and true |constraint1_Sort#RuleBody| ))

(assert |constraint0_Sort#RuleContent|)
(push)
(assert-soft (<=Sort SortK      |FreshVarSort_1_1_1_20_#KRewrite|) :id A)
(assert-soft (<=Sort SortKItem  |FreshVarSort_1_1_1_20_#KRewrite|) :id A)
(assert-soft (<=Sort SortBag    |FreshVarSort_1_1_1_20_#KRewrite|) :id A)
(assert-soft (<=Sort SortK      |VarX|) :id A)
(assert-soft (<=Sort SortKItem  |VarX|) :id A)
(assert-soft (<=Sort SortBag    |VarX|) :id A)
(assert-soft (<=Sort SortK      |VarS|) :id A)
(assert-soft (<=Sort SortKItem  |VarS|) :id A)
(assert-soft (<=Sort SortBag    |VarS|) :id A)
(assert-soft (<=Sort SortK      |FreshVarSort_1_14_1_20|) :id A)
(assert-soft (<=Sort SortKItem  |FreshVarSort_1_14_1_20|) :id A)
(assert-soft (<=Sort SortBag    |FreshVarSort_1_14_1_20|) :id A)

;(assert (not (= SortK |FreshVarSort_1_14_1_20|)))
;(assert (not (= SortKItem |FreshVarSort_1_14_1_20|)))
;(assert (not (= SortBag |FreshVarSort_1_14_1_20|)))
;(assert (not (= SortExps |FreshVarSort_1_14_1_20|)))
;(assert (not (= SortExp |FreshVarSort_1_14_1_20|)))
;(assert (not (= SortK |FreshVarSort_1_1_1_20_#KRewrite|)))


(check-sat)
(get-objectives)
(get-model)
