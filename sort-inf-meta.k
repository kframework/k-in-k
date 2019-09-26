module SORT-INF-META
  imports INT
  imports MAP

  syntax Sort ::= "bottom" | "int" | "exp" | "top" 
  syntax SortExpr ::= Sort
                    | SortExpr "/\\" SortExpr
  syntax Variable ::= r"[A-Z]"          [token]
  syntax Symbol ::= r"[a-z][a-z]*"      [token]
                  | "f" [token]
  syntax Term ::= Symbol | Variable
                | "apply" "(" Symbol Term Term ")"
                | amb(Term, Term)

  syntax Set ::= getDirectParents(Sort) [function]
  rule getDirectParents(bottom) => SetItem(int) SetItem(exp)
  rule getDirectParents(int) => SetItem(exp) SetItem(top)
  rule getDirectParents(exp) => SetItem(top)
  rule getDirectParents(top) => .Set

  syntax Bool ::= isSubsortDirect(Sort, Sort) [function]
  rule isSubsortDirect(X, Y) => Y in getDirectParents(X)

  syntax Bool ::= isSubsort(Sort, Sort) [function]
  syntax Bool ::= isSubsortSet(Set, Sort) [function]
  rule isSubsort(P, C) => isSubsortSet(SetItem(P), C)
  rule isSubsortSet(SetItem(C) Ps, C) => true
  rule isSubsortSet(SetItem(P) Ps, C)
    => isSubsortSet(getDirectParents(P) Ps, C) [owise]

  syntax Sort ::= getReturnSort(Symbol) [function]
  syntax Sort ::= getArgSort(Symbol, Int) [function]
  rule getReturnSort(f) => exp
  rule getArgSort(f, 0) => exp
  rule getArgSort(f, 1) => int

  configuration <k> $PGM:Term ~> #save </k>
                <tenv> .Map </tenv>
                <solns> .K </solns>

  syntax Term ::= "#hole"
  rule <k> apply( S HOLE T2 )
        => HOLE ~> apply( S #hole T2 )
           ...
       </k>
       <tenv> RHO </tenv>

    requires notBool HOLE in_keys(RHO)
  rule <k> HOLE ~> apply( S #hole T2 )
        => apply( S HOLE T2 )
           ...
       </k>
       <tenv> RHO </tenv>
    requires HOLE in_keys(RHO)

  rule <k> apply( S T1 HOLE )
        => HOLE ~> apply( S T1 #hole )
           ...
       </k>
       <tenv> RHO </tenv>
    requires notBool HOLE in_keys(RHO)
  rule <k> HOLE ~> apply( S T1 #hole )
        => apply( S T1 HOLE )
           ...
       </k>
       <tenv> RHO </tenv>
    requires HOLE in_keys(RHO)

  // Initially, variables are completely unconstrained
  rule <k> X:Variable ... </k>
       <tenv> (.Map => X |-> top) RHO </tenv>
    requires notBool X in_keys(RHO) 

  // As subterms appear in larger terms, we add constraints.
  rule <k> apply( S T1 T2 ) #as T ... </k>
       <tenv> (.Map => T |-> getReturnSort(S))
              T1 |-> (S1 => S1 /\ getArgSort(S, 0))
              T2 |-> (S2 => S2 /\ getArgSort(S, 1))
              RHO
       </tenv>
    requires notBool T in_keys(RHO) 

  rule <k> amb(A, B)
        => A ~> #save ~> #pop(RHO) ~> B
           ...
       </k>
       <tenv> RHO </tenv>

  syntax KItem ::= "#save"
  rule <k> (T ~> #save) => .K ... </k>
       <solns> .K => RHO ... </solns>
       <tenv> RHO => .Map </tenv>
    requires T in_keys(RHO) 

  syntax KItem ::= "#pop" "(" Map ")"
  rule <k> #pop(NEW) => .K ... </k>
       <solns> .K => RHO ... </solns>
       <tenv> RHO:Map => NEW </tenv>

endmodule
