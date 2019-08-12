Parse Outer
-----------

```k
module PARSE-OUTER
  imports KINK-CONFIGURATION
  imports PARSER-UTIL

  // TODO: remove: #writeStringToFile, #doSystem, #doSystemGetOutput, #doParseAST
  syntax KItem ::= "#parseOuter"
  rule <k> PGM:Any ~> #parseOuter => parseOuter(tokenToString(PGM)) ... </k>
endmodule
```

Parse Program
-------------

```k
module PARSER-GEN-HELPERS
  imports SET
  imports STRING-SYNTAX
  imports KINK-CONFIGURATION
  imports KORE-HELPERS
  imports META-ACCESSORS
  
  syntax KItem ::= "#collectGrammar" "(" ModuleName "," Set ")"
  rule <k> #collectGrammar(MainMod, (SetItem(MName:ModuleName) => #getLocalProds(MName)) _:Set) ... </k>

  rule <k> #collectGrammar(MName, PRODS) => .K ... </k>
       <name> MName </name>
       <grammar> .Set => PRODS </grammar>
       <s> #STUCK() => .K ... </s>

  syntax UpperName ::= String2UpperName (String) [function, functional, hook(STRING.string2token)]
  syntax Set ::= "noCastSortsInit" [function]
  rule noCastSortsInit => // sorts from this list do not receive productions for casting
        SetItem(String2UpperName("Cell"))
        SetItem(String2UpperName("CellName"))
        SetItem(String2UpperName("CellProperties"))
        SetItem(String2UpperName("CellProperty"))
        SetItem(String2UpperName("KConfigVar"))
        SetItem(String2UpperName("KLabel"))
        SetItem(String2UpperName("KList"))
        SetItem(String2UpperName("KString"))
        SetItem(String2UpperName("KVariable"))
        SetItem(String2UpperName("Layout"))
        SetItem(String2UpperName("RuleBody"))
        SetItem(String2UpperName("RuleContent"))
        SetItem(String2UpperName("OptionalDots"))
  syntax Set ::= "noLatticeSortsInit" [function]
  rule noLatticeSortsInit => // sorts from this list are not included in the automatic subsorts lattice
        SetItem(String2UpperName("Cell"))
        SetItem(String2UpperName("CellName"))
        SetItem(String2UpperName("CellProperties"))
        SetItem(String2UpperName("CellProperty"))
        SetItem(String2UpperName("K"))
        SetItem(String2UpperName("KBott"))
        SetItem(String2UpperName("KConfigVar"))
        SetItem(String2UpperName("KLabel"))
        SetItem(String2UpperName("KList"))
        SetItem(String2UpperName("KString"))
        SetItem(String2UpperName("KVariable"))
        SetItem(String2UpperName("Layout"))
        SetItem(String2UpperName("RuleBody"))
        SetItem(String2UpperName("RuleContent"))
        SetItem(String2UpperName("OptionalDots"))
           
  // Add parsing syntax
  // casts: Sort ::= Sort ":Sort"
  syntax KItem ::= "#addCasts" "(" ModuleName "," Set ")"
  rule <k> #addCasts(MName, NOCASTSORTS (.Set => SetItem(SORT))) ... </k>
       <name> MName </name>
       <grammar> SetItem(kSyntaxProduction(SORT, PROD))
         (.Set => SetItem(
          kSyntaxProduction(SORT, 
              kProductionWAttr(kProduction(nonTerminal(SORT), 
                                           terminal(String2EKoreKString("\":" +String token2String(SORT) +String "\""))),
                               kAttributesDeclaration(consAttrList(
                                  tagContent(#token("klabel","LowerName"),
                                             String2TagContents("SemanticCastTo" +String token2String(SORT))),dotAttrList(.KList)))))))
          ...
       </grammar>
     requires notBool(SORT in NOCASTSORTS)
  
  rule <k> #addCasts(_, _) => .K ... </k>
       <s> #STUCK() => .K ... </s>
  
  // subsorts: K ::= Sort, Sort ::= KBott
  syntax KItem ::= "#addSubsorts" "(" ModuleName "," Set ")"
  rule <k> #addSubsorts(MName, NOCASTSORTS (.Set => SetItem(SORT))) ... </k>
       <name> MName </name>
       <grammar> SetItem(kSyntaxProduction(SORT, PROD))
              (.Set => 
              SetItem(kSyntaxProduction(String2UpperName("K"), kProductionWAttr(nonTerminal(SORT), noAtt)))
              SetItem(kSyntaxProduction(SORT, kProductionWAttr(nonTerminal(String2UpperName("KBott")), noAtt))))
          ...
       </grammar>
     requires notBool(SORT in NOCASTSORTS)

  rule <k> #addSubsorts(_, _) => .K ... </k>
       <s> #STUCK() => .K ... </s>

endmodule

module PARSE-PROGRAM
  imports KINK-CONFIGURATION
  imports K-PRODUCTION-ABSTRACT
  imports EKORE-KSTRING-ABSTRACT
  imports KORE-HELPERS
  imports STRING
  imports FILE-UTIL
  imports PARSER-UTIL

  syntax KItem ::= "#parseProgramPath" "(" String ")" // Program Filename
                 | "#parseProgram" "(" IOString ")" // Program content
                 | "#collectGrammar"
  rule <k> #parseProgramPath(PGM_FILENAME) => #parseProgram(readFile(PGM_FILENAME)) ... </k>

  rule <k> #parseProgram(PGM)
        => parseWithProductions(GRAMMAR, "Pgm", PGM)
           ...
       </k>
       <grammar> GRAMMAR </grammar>

  rule <k> #collectGrammar ... </k>
       <decl> kSyntaxProduction(SORT, PROD) #as SYNTAXDECL </decl>
       <grammar> ( .Set => SetItem(SYNTAXDECL) ) REST </grammar>
    requires notBool(SYNTAXDECL in REST)
  rule <k> #collectGrammar => .K ... </k>
       <s> #STUCK() => .K ... </s>
endmodule
```

Parse Config
-------------

```k
module PARSE-CONFIG
  imports RULES-WITH-BUBBLES-COMMON
  imports KINK-CONFIGURATION
  imports K-PRODUCTION-ABSTRACT
  imports EKORE-KSTRING-ABSTRACT
  imports KORE-HELPERS
  imports STRING
  imports FILE-UTIL
  imports PARSER-UTIL
  imports KORE-ABSTRACT
  imports PARSER-GEN-HELPERS

  syntax KItem ::= "#parseConfigBubble"

  rule <k> #parseConfigBubble
        => #collectGrammar(MName, #getImportedModules(MName) #getImportedModules(#token("CONFIG-INNER", "UpperName")))
        ~> #addCasts(MName, noCastSortsInit)
        ~> #addSubsorts(MName, noLatticeSortsInit)
        ~> #finishConfigGrammar(MName)
        ~> #parseConfigBubble
       ... </k>
       <name> MName </name>
       <decl> kConfiguration(noAttrs(_:Bubble)) </decl>
       <configGrammar> .Set </configGrammar>

  rule <k> #parseConfigBubble ... </k>
       <decl> kConfiguration(noAttrs(C:Bubble)) => kConfiguration(noAttrs({parseWithProductions(GRAMMAR, "K", tokenToString(C))}:>Pattern)) </decl>
       <configGrammar> GRAMMAR </configGrammar>
     requires GRAMMAR =/=K .Set

  rule <k> #parseConfigBubble => .K ... </k>
       <s> #STUCK() => .K ... </s>

  syntax KItem ::= "#finishConfigGrammar" "(" ModuleName ")"
  rule <k> #finishConfigGrammar(MName) => .K ... </k>
       <name> MName </name>
       <grammar> PRODS => .Set </grammar>
       <configGrammar> .Set => PRODS </configGrammar>
       <s> #STUCK() => .K ... </s>
  
endmodule

module CONFIG-INFO
  imports STRING
  imports KINK-CONFIGURATION
  imports EKORE-KSTRING-ABSTRACT
  // collect config info - destructure the configuration and populate <configInfo>
  // with \dv key -> type (CellInfo or KConfigVar)
  syntax KItem ::= "#extractConfigInfo"
  syntax KItem ::= collectCellName(Patterns)
  rule <k> #extractConfigInfo => collectCellName(P) ~> #extractConfigInfo ... </k>
       <decl> kConfiguration(noAttrs(P)) </decl>
       <collected> Configs => Configs SetItem(P) </collected>
     requires notBool P in Configs

  rule <k> collectCellName( _ { _ } (A)) => collectCellName(A) ... </k>
  rule <k> collectCellName(A, B) => collectCellName(A) ~> collectCellName(B) ... </k>
  rule <k> collectCellName( .Patterns ) => .K ... </k>

  rule <k> collectCellName(\dv { Srt { .Sorts } } ( CellName )) => .K ... </k>
       <cellName> .Map => substrString(token2String(CellName), 1, lengthString(token2String(CellName)) -Int 1) |-> token2String(Srt) ... </cellName>

  rule <k> #extractConfigInfo => .K ... </k>
       <s> #STUCK() => .K ... </s>
endmodule

module PARSE-RULE
  imports RULES-WITH-BUBBLES-COMMON
  imports KINK-CONFIGURATION
  imports K-PRODUCTION-ABSTRACT
  imports EKORE-KSTRING-ABSTRACT
  imports KORE-HELPERS
  imports STRING
  imports FILE-UTIL
  imports PARSER-UTIL
  imports KORE-ABSTRACT
  imports META-ACCESSORS
  imports PARSER-GEN-HELPERS

  // parse rule bubbles
  syntax KItem ::= "#parseRuleBubble"
  rule <k> #parseRuleBubble
        => #collectGrammar(MName, #getImportedModules(MName) #getImportedModules(#token("RULE-INNER", "UpperName")))
        ~> #addCasts(MName, noCastSortsInit)
        ~> #addSubsorts(MName, noLatticeSortsInit)
        ~> #addRuleCells(MName, .Set)
        ~> #finishRuleGrammar(MName)
        ~> #parseRuleBubble
       ... </k>
       <name> MName </name>
       <decl> kRule(_) </decl>
       <ruleGrammar> .Set </ruleGrammar>
  
  rule <k> #parseRuleBubble ... </k>
       <decl> kRule(noAttrs(C:Bubble)) => kRule(noAttrs({parseWithProductions(GRAMMAR, "RuleContent", tokenToString(C))}:>Pattern)) </decl>
       <ruleGrammar> GRAMMAR </ruleGrammar>
     requires GRAMMAR =/=K .Set
  rule <k> #parseRuleBubble ... </k>
       <decl> kRule(attrs(C:Bubble, At)) => kRule(attrs({parseWithProductions(GRAMMAR, "RuleContent", tokenToString(C))}:>Pattern, At)) </decl>
       <ruleGrammar> GRAMMAR </ruleGrammar>
     requires GRAMMAR =/=K .Set

  rule <k> #parseRuleBubble => .K ... </k>
       <s> #STUCK() => .K ... </s>

  // add rule cells
  syntax KItem ::= "#addRuleCells" "(" ModuleName "," Set ")" // collector for already inserted cell productions
  rule <k> #addRuleCells(MName, Cells => Cells SetItem(CellName)) ... </k>
       <name> MName </name>
       <grammar> .Set => SetItem(
          kSyntaxProduction(#token("Cell","UpperName"), 
              kProductionWAttr(kProduction(
                  terminal(String2EKoreKString("\"<" +String CellName +String ">\"")), kProduction(
                  nonTerminal(#token("OptionalDots","UpperName")), kProduction(
                  nonTerminal(#token("K","UpperName")), kProduction(
                  nonTerminal(#token("OptionalDots","UpperName")),
                  terminal(String2EKoreKString("\"</" +String CellName +String ">\"")))))),
                kAttributesDeclaration(consAttrList(
                   tagContent(#token("klabel","LowerName"), String2TagContents(CellName +String "cell")),consAttrList(
                   tagContent(#token("cellName","LowerName"), String2TagContents(CellName)),consAttrList(
                   tagSimple(#token("cell","LowerName")), dotAttrList(.KList))))))))
          ...
       </grammar>
       <cellName> CellName |-> "CellName" ... </cellName>
     requires notBool CellName in Cells
  rule <k> #addRuleCells(_, _) => .K ... </k>
       <s> #STUCK() => .K ... </s>    

  syntax KItem ::= "#finishRuleGrammar" "(" ModuleName ")"
  rule <k> #finishRuleGrammar(MName) => .K ... </k>
       <name> MName </name>
       <grammar> PRODS => .Set </grammar>
       <ruleGrammar> .Set => PRODS </ruleGrammar>
       <s> #STUCK() => .Set ... </s>

endmodule
```

Parse into EKore
----------------

```k
module PARSE-TO-EKORE
  imports EKORE-ABSTRACT
  imports KINK-CONFIGURATION
  imports PARSER-UTIL

  syntax KItem ::= "#parseToEKore"
  rule <k> PGM:Any ~> #parseToEKore => parseEKore(tokenToString(PGM)) ... </k>
endmodule
```
