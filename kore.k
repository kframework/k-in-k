module TOKENS
  syntax UpperName
  syntax LowerName
  syntax Numbers
  syntax KModuleName ::= UpperName
  syntax KoreName    ::= UpperName | LowerName
                       | KModuleName
  syntax KSort       ::= UpperName
endmodule

// TODO: UpperName is used for K modules names and shouldn't allow primes or #s.
module TOKENS-SYNTAX
  imports TOKENS

  syntax UpperName ::= r"[A-Z][A-Za-z\\-0-9'\\#]*" [token]
  syntax LowerName ::= r"[a-z][A-Za-z\\-0-9'\\#]*" [token]
                     | "left" [token]
                     // ^ I have no idea why I need to redeclare 'left',
                     //  but it gives a parsing error otherwise

  syntax Numbers   ::= r"[\\+-]?[0-9]+"        [token]
  syntax KoreName ::= r"\\rewrites"     [token, prec(2)]
endmodule

module KORE-COMMON
  imports TOKENS
  imports STRING-SYNTAX

  syntax Sort     ::= KoreName | KoreName "{" Sorts "}" [klabel(nameParam)]
  syntax Sorts    ::= List{Sort, ","} [klabel(sortList)]
  syntax Symbol   ::= KoreName "{" Sorts "}" [klabel(symbolSorts)]
  syntax Variable ::= KoreName ":" Sort [klabel(varType)]

  syntax Pattern ::= Variable
                   | String
                   | Symbol "(" Patterns ")" [klabel(symbolParams)]
                   | "\\and"      "{" Sort "}"          "(" Pattern "," Pattern ")"
                   | "\\not"      "{" Sort "}"          "(" Pattern ")"
                   | "\\or"       "{" Sort "}"          "(" Pattern "," Pattern ")"
                   | "\\implies"  "{" Sort "}"          "(" Pattern "," Pattern ")"
                   | "\\iff"      "{" Sort "}"          "(" Pattern "," Pattern ")"
                   | "\\forall"   "{" Sort "}"          "(" Variable "," Pattern ")"
                   | "\\exists"   "{" Sort "}"          "(" Variable "," Pattern ")"
                   | "\\ceil"     "{" Sort "," Sort "}" "(" Pattern ")"
                   | "\\floor"    "{" Sort "," Sort "}" "(" Pattern ")"
                   | "\\equals"   "{" Sort "," Sort "}" "(" Pattern "," Pattern ")"
                   | "\\in"       "{" Sort "," Sort "}" "(" Pattern "," Pattern ")"
                   | "\\top"      "{" Sort "}"          "(" ")"
                   | "\\bottom"   "{" Sort "}"          "(" ")"
                   | "\\next"     "{" Sort "}"          "(" Pattern ")"
                // | "\\rewrites" "{" Sort "}"          "(" Pattern "," Pattern ")" // commented so it makes visiting easier
                   | "\\dv"       "{" Sort "}"          "(" Pattern ")"
  syntax Patterns ::= List{Pattern, ","} [klabel(patternList)]

  syntax Attribute ::= "[" Patterns "]"

  syntax Declaration ::=
      "import"      KoreName                                          Attribute
    | "sort"        KoreName "{" KoreNames "}"                        Attribute
    | "hook-sort"   KoreName "{" KoreNames "}"                        Attribute
    | "symbol"      KoreName "{" KoreNames "}" "(" Sorts ")" ":" Sort Attribute
    | "hook-symbol" KoreName "{" KoreNames "}" "(" Sorts ")" ":" Sort Attribute
    | "axiom"                "{" KoreNames "}" Pattern                Attribute
  syntax Declarations ::= List{Declaration, ""} [klabel(declList), format(%1%2%n%3)]

  syntax KoreNames ::= List{KoreName, ","} [klabel(nameList)]

  syntax KoreModule ::= "module" KoreName Declarations "endmodule" Attribute [klabel(koreModule), format(%1 %2%i%n%3%n%d%4 %5)]
  syntax Module ::= KoreModule
  syntax Modules ::= List{Module, ""} [klabel(koreModules), format(%1%2%n%3)]

  syntax KoreDefinition ::= Attribute Modules [klabel(koreDefinition), format(%1%n%n%2)]
  syntax Definition ::= KoreDefinition
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

  syntax Modules ::= Modules "++Modules" Modules [function]
  rule (M1 MS1) ++Modules MS2 => M1 (MS1 ++Modules MS2)
  rule .Modules ++Modules MS2 => MS2

  syntax Bool ::= Pattern "inPatterns" Patterns                      [function]
  rule (P inPatterns           .Patterns) => false
  rule (P inPatterns P:Pattern  ,  PS)    => true
  rule (P inPatterns P1:Pattern ,  PS)
    => (P inPatterns               PS)
    requires notBool P ==K P1
endmodule

