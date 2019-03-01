```k
module TOKENS
  // Lexical
  syntax UpperName
  syntax LowerName
  syntax DollarName
  syntax Numbers
  syntax BacktickName

  // Abstract
  syntax KModuleName ::= UpperName
  syntax KSort       ::= UpperName
  syntax ModuleName  ::= KModuleName | UpperName | LowerName
  syntax SymbolName  ::= UpperName | LowerName
  syntax SortName    ::= KSort | UpperName | LowerName
  syntax VariableName ::= UpperName | LowerName
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
  syntax DollarName ::= r"(\\$)([A-Z][A-Za-z\\-0-9]*)" [token]
  syntax BacktickName ::= r"`(\\\\`|\\\\\\\\|[^`\\\\\\n\\r])+`" [token]
endmodule

module KORE-COMMON
  imports TOKENS

  syntax Sort     ::= SortName | SortName "{" Sorts "}" [klabel(nameParam)]
  syntax Sorts
  syntax Symbol   ::= SymbolName "{" Sorts "}" [klabel(symbolSorts)]
  syntax Variable ::= VariableName ":" Sort [klabel(varType)]

  syntax Pattern ::= Variable
                // | String
                   | Symbol "(" Patterns ")" [klabel(application)]
                   | "\\and"      "{" Sort "}"          "(" Pattern "," Pattern ")"
                   | "\\not"      "{" Sort "}"          "(" Pattern ")"
                   | "\\or"       "{" Sort "}"          "(" Pattern "," Pattern ")"
                   | "\\implies"  "{" Sort "}"          "(" Pattern "," Pattern ")"
                   | "\\iff"      "{" Sort "}"          "(" Pattern "," Pattern ")"
                   | "\\forall"   "{" Sort "}"          "(" Variable "," Pattern ")"
                   | "\\exists"   "{" Sort "}"          "(" Variable "," Pattern ")"
                   | "\\ceil"     "{" Sort "," Sort "}" "(" Pattern ")"
                   | "\\floor"    "{" Sort "," Sort "}" "(" Pattern ")"
                   | "\\equals"   "{" Sort "," Sort "}" "(" Pattern "," Pattern ")" [klabel(equals)]
                   | "\\in"       "{" Sort "," Sort "}" "(" Pattern "," Pattern ")"
                   | "\\top"      "{" Sort "}"          "(" ")"
                   | "\\bottom"   "{" Sort "}"          "(" ")"
                   | "\\next"     "{" Sort "}"          "(" Pattern ")"
                // | "\\rewrites" "{" Sort "}"          "(" Pattern "," Pattern ")" // commented so it makes visiting easier
                   | "\\dv"       "{" Sort "}"          "(" Pattern ")"
  syntax Patterns

  syntax Attribute ::= "[" Patterns "]" [klabel(koreAttributes)]

  syntax SortDeclaration ::= "sort" Sort Attribute [klabel(sortDeclaration)]
  syntax SymbolDeclaration ::= "symbol" Symbol "(" Sorts ")" ":" Sort Attribute [klabel(symbolDeclaration)]
  syntax KoreDeclaration ::=
      "import" ModuleName Attribute [klabel(koreImports)]
    | "hook-sort" Sort Attribute
    | "hook-symbol" Symbol "(" Sorts ")" ":" Sort Attribute
    | "axiom" "{" Sorts "}" Pattern Attribute [klabel(axiomDeclaration)]
    | SortDeclaration
    | SymbolDeclaration
  syntax Declaration ::= KoreDeclaration
  syntax Declarations

  syntax KoreModule ::= "module" ModuleName Declarations "endmodule" Attribute [klabel(koreModule), format(%1 %2%i%n%3%n%d%4 %5%n)]
  syntax Module ::= KoreModule
  syntax Modules

  syntax KoreDefinition ::= Attribute Modules [klabel(koreDefinition), format(%1%n%n%2)]
  syntax Definition ::= KoreDefinition
endmodule

module KORE-SYNTAX
  imports KORE-COMMON
  imports TOKENS-SYNTAX

  syntax EmptySorts ::= ""               [klabel(dotSorts )]
  syntax NeSorts    ::= Sort "," NeSorts [klabel(consSorts)]
                      | Sort EmptySorts  [klabel(consSorts)]
  syntax Sorts ::= NeSorts | EmptySorts

  syntax EmptyPatterns ::= ""                  [klabel(dotPatterns )]
  syntax NePatterns    ::= Pattern "," NePatterns [klabel(consPatterns)]
                         | Pattern EmptyPatterns  [klabel(consPatterns)]
  syntax Patterns ::= NePatterns | EmptyPatterns

  syntax EmptyDeclarations ::= ""               [klabel(dotDeclarations )]
  syntax NeDeclarations    ::= Declaration NeDeclarations [klabel(consDeclarations)]
                             | Declaration EmptyDeclarations  [klabel(consDeclarations)]
  syntax Declarations ::= NeDeclarations | EmptyDeclarations

  syntax EmptyModules ::= ""               [klabel(dotModules )]
  syntax NeModules    ::= Module NeModules [klabel(consModules)]
                        | Module EmptyModules  [klabel(consModules)]
  syntax Modules ::= NeModules | EmptyModules
endmodule

module KORE-ABSTRACT
  imports KORE-COMMON

  syntax Sorts ::= Sort "," Sorts        [klabel(consSorts)]
                 | ".Sorts"              [klabel(dotSorts )]

  syntax Patterns ::= Pattern "," Patterns [klabel(consPatterns)]
                    | ".Patterns"          [klabel(dotPatterns )]

  syntax Declarations ::= Declaration Declarations [klabel(consDeclarations), format(%1%n%2)]
                    | ".Declarations"              [klabel(dotDeclarations )]

  syntax Modules ::= Module Modules [klabel(consModules), format(%1%n%2)]
                    | ".Modules"    [klabel(dotModules )]
endmodule
```
