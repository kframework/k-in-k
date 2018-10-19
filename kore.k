// Written by Xiaohong Chen (hreada)

module TOKENS
  syntax UpperName
  syntax LowerName
  syntax Numbers
  syntax KoreName    ::= UpperName | LowerName
  syntax KModuleName ::= UpperName
  syntax KSort       ::= UpperName
endmodule

// TODO: UpperName is used for K modules names and shouldn't allow primes or #s.

module TOKENS-SYNTAX
  imports TOKENS

  syntax UpperName ::= r"[A-Z][A-Za-z\\-0-9'\\#]*" [token]
  syntax LowerName ::= r"[a-z][A-Za-z\\-0-9'\\#]*" [token]
                     | "left" [token] // I have no idea why I need to redeclare 'left', but it gives a parsing error otherwise
  syntax Numbers   ::= r"[\\+-]?[0-9]+"        [token]

  syntax KoreName ::= r"\\rewrites"     [token, prec(2)]
endmodule


module KORE-COMMON
  imports TOKENS
  imports STRING-SYNTAX

  syntax Sort ::= KoreName | KoreName "{" Sorts "}" [klabel(nameParam)]

  syntax Sorts ::= List{Sort, ","} [klabel(sortList)]

  syntax Symbol ::= KoreName "{" Sorts "}" [klabel(symbolSorts)]

  syntax Variable ::= KoreName ":" Sort [klabel(varType)]

  syntax Pattern ::= Variable
                   | String
                   | Symbol "(" Patterns ")" [klabel(symbolParams)]
                   | "\\and" "{" Sort "}" "(" Pattern "," Pattern ")"
                   | "\\not" "{" Sort "}" "(" Pattern ")"
                   | "\\or"  "{" Sort "}" "(" Pattern "," Pattern ")"
                   | "\\implies"  "{" Sort "}" "(" Pattern "," Pattern ")"
                   | "\\iff"  "{" Sort "}" "(" Pattern "," Pattern ")"
                   | "\\forall" "{" Sort "}" "(" Variable "," Pattern ")"
                   | "\\exists" "{" Sort "}" "(" Variable "," Pattern ")"
                   | "\\ceil" "{" Sort "," Sort "}" "(" Pattern ")"
                   | "\\floor" "{" Sort "," Sort "}" "(" Pattern ")"
                   | "\\equals"  "{" Sort "," Sort "}" "(" Pattern "," Pattern ")"
                   | "\\in" "{" Sort "," Sort "}" "(" Pattern "," Pattern ")"
                   | "\\top" "{" Sort "}" "(" ")"
                   | "\\bottom" "{" Sort "}" "(" ")"
                   | "\\next" "{" Sort "}" "(" Pattern ")"
                   //| "\\rewrites" "{" Sort "}" "(" Pattern "," Pattern ")" // commented so it makes visiting easier
                   | "\\dv" "{" Sort "}" "(" Pattern ")"

  syntax Patterns ::= List{Pattern, ","} [klabel(patternList)]

  syntax Attribute ::= "[" Patterns "]"

  syntax Declaration ::=
    "import" KoreName Attribute
  | "sort" KoreName "{" KoreNames "}" Attribute
  | "hook-sort" KoreName "{" KoreNames "}" Attribute
  | "symbol" KoreName "{" KoreNames "}" "(" Sorts ")" ":" Sort Attribute
  | "hook-symbol" KoreName "{" KoreNames "}" "(" Sorts ")" ":" Sort Attribute
  | "axiom" "{" KoreNames "}" Pattern Attribute

  syntax KoreNames ::= List{KoreName, ","} [klabel(nameList)]

  syntax Declarations ::= List{Declaration, ""} [klabel(declList), format(%1%2%n%3)]

  syntax Module ::= "module" KoreName Declarations "endmodule" Attribute [klabel(module), format(%1 %2%i%n%3%n%d%4 %5)]

  syntax Modules ::= List{Module, ""} [klabel(moduleList), format(%1%2%n%3)]

  syntax Definition ::= Attribute Modules [klabel(definition), format(%1%n%n%2)]

endmodule

module KORE-SYNTAX
  imports KORE-COMMON
  imports TOKENS-SYNTAX
endmodule

module KORE-HELPERS
  imports KORE-COMMON
  imports DOMAINS

  syntax Declarations ::= Declarations "++Declarations" Declarations [function]
  rule (D1 DS1) ++Declarations DS2 => D1 (DS1 ++Declarations DS2)
  rule .Declarations ++Declarations DS2 => DS2 

  syntax Bool ::= Pattern "inPatterns" Patterns                      [function]
  rule (P inPatterns           .Patterns) => false
  rule (P inPatterns P:Pattern  ,  PS)    => true
  rule (P inPatterns P1:Pattern ,  PS)
    => (P inPatterns               PS)
    requires notBool P ==K P1
endmodule

module KORE

  imports KORE-COMMON  // don't import KORE-SYNTAX

  //configuration <T> <k> $PGM:Definition </k> </T>

  // unit element for \or
  rule \or{_}(X, \bottom{_}()) => X [anywhere]
  rule \or{_}(\bottom{_}(), X) => X [anywhere]
  // \or(X, X) => X
  rule \or{_}(X, X) => X [anywhere]

  syntax KoreName ::= "inj" [token, prec(2)]

  // inj composition - performs a similar step to TreeCleanerVisitor.java
  rule inj{Y,Z}(inj{X,Y}(W)) => inj{X,Z}(W) [anywhere]

endmodule
