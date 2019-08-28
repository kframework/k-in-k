module SORT-INF
  imports INT
  imports BOOL
  imports MAP

  configuration <sortInf>
                  <k> $PGM:Exp </k>
                  <sortEnv> .Map </sortEnv>
                </sortInf>

  // base syntax
  syntax Sort ::= "int" | "exp"

  syntax Id ::= "x" | "y"
  syntax Exp ::= Id | Int
               | Exp "+"  Exp [seqstrict]
               | Exp "+i" Exp [seqstrict]
               | Exp "ie" Exp [seqstrict]

  // Since we are evaluating expressions to their sorts:
  syntax KResult ::= Sort
  syntax Exp ::= Sort

  rule <k> X:Id => ?S:Sort ... </k>
       <sortEnv> (.Map => (X |-> ?S)) RHO </sortEnv>
    requires notBool(X in_keys(RHO))
  rule <k> X:Id => S ... </k>
       <sortEnv> ... X |-> S ... </sortEnv>

  rule <k> int => exp ... </k>
  rule <k> exp + exp => exp ... </k>
  rule <k> int ie exp => int ... </k>
  rule <k> int +i int => int ... </k>
endmodule

/*
module SORT-INF
  imports BOOL
  imports MAP
  imports STRING

  configuration <sortInf>
                  <k> #init ~> $PGM:Pattern </k>
                  <sortEnv> .Map </sortEnv>
                  <prods>
                    <prodx multiplicity="*" type="Set"> ?_:Prod </prodx>
                  </prods>
                </sortInf>
  
  syntax Sort ::= sort(String)
  syntax Prod ::= inj(Sort, Sort)
                | prod(String, Sort)
                | prod(String, Sort, Sort)
                | prod(String, Sort, Sort, Sort)

  syntax Id ::= "x" | "y"
  syntax Pattern ::= Id
                 | appl1(String, Pattern)           [seqstrict(2)]
                 | appl2(String, Pattern, Pattern)  [seqstrict(2, 3)]

  syntax KItem ::= "#init"
  rule <k> #init => appl2("+", x, y) ... </k>
       <prods> _
            => <prodx> prod("+", sort("exp"), sort("exp"), sort("exp")) </prodx>
               <prodx> prod("+i", sort("int"), sort("int"), sort("int")) </prodx>
       </prods>

  syntax Pattern ::= Sort
  syntax KResult ::= Sort

  rule <k> X:Id => ?S:Sort ... </k>
       <sortEnv> .Map => (X |-> ?S) ... </sortEnv>
  rule <k> appl2(SYM, ARG1, ARG2) => RESULT ... </k>
       <prodx> prod(SYM, RESULT, ARG1, ARG2) </prodx>
endmodule
*/
