## Introduction
We want to infer types for variables so that the rule has the most chances to apply therefore we want to
maximize the inferred sorts. Because of the way we mix user syntax with K syntax, we introduce a new subsort
between `K` and `KBott` for every user sort. To make this easier to visualize we can think of all the subsort relations as a DAG where `K` is at the top and `KBott` is the smallest element. Inferring a sort means finding the highest sort from the graph which meets all the constraints.

Let's take an example (1):
```
// A < B < C < D
syntax D ::= C
syntax C ::= B
syntax B ::= A
syntax A ::= f(C)
rule f(X) => .K
```
The sort of `X` can be any of `A`, `B` or `C`. But to maximize matching we must infer `C`.

### Why we need a constraint solver to disambiguate properly?

Let's take this example (2):
```
syntax Exps  ::= Exp “,” Exps | Exp
syntax Exp   ::= Id
syntax Id    ::= [A-Za-z][A-Za-z0-9]*
syntax Stmt  ::= “val” Exps “;” Stmt
syntax KBott ::= “(“ K “)” | “(“ Id “,” Stmt “)”
syntax K     ::= Exps | Exp | Id
rule val X; S => (X,S)
rule =>(val_;_(X:Exps, S:Stmt), 
        amb((_)(_,_(X:Exp, S:Exps))
            (_,_)(  X:Id,  S:Stmt))
```
Based on each appearance of each variable and ambiguities we have the following constraints:
```
variant 1: - no solution
  X:{Exps, Exp}
  S:{Stmt, Exps}
variant 2:
  X:{Exps, Id}
  S:{Stmt, Stmt}
```
For variant 1, we can infer `X:Exp` as being the most general sort that fits all constraints, but for `S` we end up with `KBott` which is not going to match on anything. So we have to discard this solution.
Variant 2 will infer `X:Id`, which is smaller than the previous solution, but we can find a valid option for `S:Stmt` this time. We can take this solution and, with a simple visitor, can eliminate the rest of the ambiguities from the AST.

Type inference here can be viewed as a constraint solving problem where we must solve `X` and `S` in:
```
X:Exps /\ S:Stmt /\ ((X:Exp /\ S:Exps) \/ (X:Id /\ S:Stmt))
```

## Modeling in SMT
After playing with Z3 for a bit, we ended up working with CVC4 because of their builtin support for Sets.

First step in modeling the problem was to represent the sorts and the subsort relations in SMT2.
```
(declare-datatypes ((Sort 0))
   (((A) (B) (C) (D))))

; A < B < C < D
(define-fun tsubs () (Set (Tuple Sort Sort))
  (tclosure (insert ; initial subsorts
    (mkTuple A B)
    (mkTuple B C) (singleton
    (mkTuple C D)))))
```
We introduce the sort names as datatypes and the subsort relations as a set of tuples, transitively closed.
```
(define-fun isSubsortedStrict ((x Sort) (y Sort)) Bool
   (member (mkTuple x y) tsubs))
(define-fun isSubsorted ((x Sort) (y Sort)) Bool
   (or (= x y) (isSubsortedStrict x y)))
```
Subsorting can be represented as uninterpreted functions which just simply check membership of the relation in question in the `tsubs` set.

Modeling the constraints on `X` is as simple as:
```
(declare-const X Sort)
(assert (and (isSubsorted X C))) ; constraints on variable
```
At this point, the SMT solver would find any of the `A`, `B`, or `C` sorts as satisfiable. To make sure we get the maximum, we must add a new constraint:
```
(assert (not (exists ((y Sort))  ; maximality
                (and (isSubsorted y C)
                     (isSubsortedStrict X y)))))
```
which says that there is no `y` which is strictly bigger than `X` and meets the same constraints.

The final step is to model multiple variables at the same time. For this, we define a solution as being a tuple of Sorts on which we apply the same restrictions as above.

Here is how example (2) would look like:
```
(set-logic ALL)
(set-info :status sat)
; use finite model finding heuristic for quantifier instantiation
(set-option :finite-model-find true)
(set-option :produce-models true)
(declare-datatypes ((Sort 0))
   (((Id) (Exp) (Exps) (Stmt))))

; Id < Exp < Exps

; subsorts POSet
(define-fun tsubs () (Set (Tuple Sort Sort))
    (tclosure (insert
        (mkTuple Id Exp) (singleton
        (mkTuple Exp Exps)))))

(define-fun isSubsortedStrict ((x Sort) (y Sort)) Bool
   (member (mkTuple x y) tsubs))
(define-fun isSubsorted ((x Sort) (y Sort)) Bool
   (or (= x y) (isSubsortedStrict x y)))

; constraints predicate: rule var X; S => (X, S)
(define-fun constraints ((x Sort) (s Sort)) Bool
    (and (isSubsorted x Exps)
         (isSubsorted s Stmt)
         (or (and (isSubsorted x Exp)
                  (isSubsorted s Exps))
             (and (isSubsorted x Id)
                  (isSubsorted s Stmt)))))

; maximality
(define-fun maximality ((x Sort) (s Sort)) Bool
    (not (exists ((xp Sort) (sp Sort))
                (and (constraints xp sp)
                     (or (isSubsortedStrict x xp)
                         (isSubsortedStrict s sp))))))

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
```
Output: `(define-fun solSet () (Set (Tuple Sort Sort)) (singleton (mkTuple Id Stmt)))`

Since we don't always have a top sort, we may end up with multiple solutions. CVC4 allows us to find all the solutions by adding a "completeness" assert.
```
(set-logic ALL)
(set-info :status sat)
; use finite model finding heuristic for quantifier instantiation
(set-option :finite-model-find true)
(set-option :produce-models true)
(declare-datatypes ((Sort 0))
   (((A) (B) (C))))

; A < B C

; subsorts POSet
(define-fun tsubs () (Set (Tuple Sort Sort))
    (tclosure (insert
        (mkTuple A B) (singleton
        (mkTuple A C)))))

(define-fun isSubsortedStrict ((x Sort) (y Sort)) Bool
   (member (mkTuple x y) tsubs))
(define-fun isSubsorted ((x Sort) (y Sort)) Bool
   (or (= x y) (isSubsortedStrict x y)))

; constraints predicate
(define-fun constraints ((x Sort)) Bool
    (or (isSubsorted x B)
        (isSubsorted x C)))

; maximality
(define-fun maximality ((x Sort)) Bool
    (not (exists ((xp Sort))
                (and (constraints xp)
                     (isSubsortedStrict x xp)))))

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
```
Output: `(define-fun solSet () (Set (Tuple Sort)) (union (singleton (mkTuple B)) (singleton (mkTuple C))))`

### Extra details
1. The CVC4 option is important: `(set-option :finite-model-find true)` use finite model finding heuristic for quantifier instantiation.
2. To extract the solution just take every tuple from the `solSet` and match it with the same variables used at generation time.
3. Not modeled here, but it is possible to have no solution for certain variables. In order to still provide the user with useful feedback, we can forcefully add a `KBott` sort as a bottom, which ensures that the SMT solver will always find a solution. Then it's just a matter of post-processing to find the correct solution and return an error when needed.

## TODO:
### Overloaded productions
```
syntax Exp  ::= Id
syntax Ids  ::= Id  "," Ids  | Id
syntax Exps ::= Exp "," Exps | Exp | Ids
rule A, B => .K
```
```
rule =>(amb(ids(A:Id, B:Ids), exps(A:Exp, B:Exps)), .K)
variant 1:
  A:{Id}
  B:{Ids}
variant 2:
  A:{Exp}
  B:{Exps}
```
Both solutions are valid, but the second one is more
general than the first (all sorts are subsorts) so we
choose variant 2, then prune all ambiguities.
It's possible that in other parts of the rule we have
additional constraints and end up choosing variant 1.
Then we are still left with ambiguities, then we apply
a filter for overloaded productions. Prod1 < Prod2 if
all NT1 <= NT2. In this case ids < exps.

### Priority and associativity
```
syntax Exp ::= Exp "*" Exp [left]
             > Exp "+" Exp [left]
rule 1 + 2 * 3 => .K
rule =>(amb(plus(1, mul(2,3)), mul(plus(1,2),3)), .K)
```
we eliminate the second branch simply because mul is a direct
parent of plus. Associativity looks at direct parent-child
relations in the left hand side or right hand side only.
