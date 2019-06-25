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

  syntax UpperName ::= r"[A-Z][A-Za-z\\-0-9'\\#]*" [token, autoReject]
  syntax LowerName ::= r"[a-z][A-Za-z\\-0-9'\\#]*" [token, autoReject]
                     | "left" [token]
                     // ^ I have no idea why I need to redeclare 'left',
                     //  but it gives a parsing error otherwise
  syntax Numbers   ::= r"[\\+-]?[0-9]+"        [token]
  syntax DollarName ::= r"(\\$)([A-Z][A-Za-z\\-0-9]*)" [token]
  syntax BacktickName ::= r"`(\\\\`|\\\\\\\\|[^`\\\\\\n\\r])+`" [token]
endmodule

module KORE-COMMON
  imports TOKENS
  syntax LowerName ::= "function"    [token]
                     | "functional"  [token]
                     | "constructor" [token]
                     | "injective"   [token]
                     | "klabel"      [token]

  syntax Sort     ::= SortName | SortName "{" Sorts "}" [klabel(nameParam)]
  syntax Sorts
  syntax Symbol   ::= SymbolName "{" Sorts "}" [klabel(symbolSorts)]
  syntax Variable ::= VariableName ":" Sort [klabel(varType)]

  syntax Pattern ::= Variable
                // | String
                   | Symbol "(" Patterns ")" [klabel(application)]
                   | "\\and"      "{" Sort "}"          "(" Pattern "," Pattern ")"  [klabel(and)]
                   | "\\not"      "{" Sort "}"          "(" Pattern ")"              [klabel(not)]
                   | "\\or"       "{" Sort "}"          "(" Pattern "," Pattern ")"  [klabel(or)]
                   | "\\implies"  "{" Sort "}"          "(" Pattern "," Pattern ")"  [klabel(implies)]
                   | "\\iff"      "{" Sort "}"          "(" Pattern "," Pattern ")"  [klabel(iff)]
                   | "\\forall"   "{" Sort "}"          "(" Variable "," Pattern ")" [klabel(forall)]
                   | "\\exists"   "{" Sort "}"          "(" Variable "," Pattern ")" [klabel(exists)]
                   | "\\ceil"     "{" Sort "," Sort "}" "(" Pattern ")"              [klabel(ceil)]
                   | "\\floor"    "{" Sort "," Sort "}" "(" Pattern ")"              [klabel(floor)]
                   | "\\equals"   "{" Sort "," Sort "}" "(" Pattern "," Pattern ")"  [klabel(equals)]
                   | "\\in"       "{" Sort "," Sort "}" "(" Pattern "," Pattern ")"  [klabel(in)]
                   | "\\top"      "{" Sort "}"          "(" ")"                      [klabel(top)]
                   | "\\bottom"   "{" Sort "}"          "(" ")"                      [klabel(bottom)]
                   | "\\next"     "{" Sort "}"          "(" Pattern ")"              [klabel(next)]
                   | "\\rewrites" "{" Sort "}"          "(" Pattern "," Pattern ")"  [klabel(rewrites)]
                   | "\\dv"       "{" Sort "}"          "(" Pattern ")"              [klabel(dv)]
  syntax Patterns

  syntax Attribute ::= "[" Patterns "]" [klabel(koreAttributes)]

  syntax KoreDeclaration ::=
      "import" ModuleName Attribute [klabel(koreImport)]
    | "hook-sort" Sort Attribute
    | "hook-symbol" Symbol "(" Sorts ")" ":" Sort Attribute
    | "sort" Sort Attribute [klabel(sortDeclaration)]
    | "symbol" Symbol "(" Sorts ")" ":" Sort Attribute [klabel(symbolDeclaration)]
    | "axiom" "{" Sorts "}" Pattern Attribute [klabel(axiomDeclaration)]
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
  
  syntax Layout ::= r"(/\\*([^\\*]|(\\*+([^\\*/])))*\\*+/|//[^\n\r]*|[\\ \n\r\t])*" [klabel(layout)]
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
