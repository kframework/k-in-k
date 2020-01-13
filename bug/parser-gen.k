
require "parser-disamb.k"

module PARSER-GEN-HELPERS
  imports SET
  imports STRING-SYNTAX
  imports KINK-CONFIGURATION
  imports KORE-HELPERS
  imports META-ACCESSORS

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
  // expecting a list of productions as argument and returns a new list with added cast for each sort found
  // except for `noCastSortsInit`
  syntax String ::= token2String(UpperName) [function, functional, hook(STRING.token2string)]
  syntax Set ::= "#addCasts" "(" Set ")" [function]
  syntax Set ::= "#addCasts2" "(" Set "," Set ")" [function]
  rule #addCasts(Prds) => #addCasts2(Prds, noCastSortsInit)
  rule #addCasts2(
          SetItem(kSyntaxProduction(SORT, PROD))
          _:Set
          (.Set => SetItem(
            kSyntaxProduction(SORT,
                kProductionWAttr(kProduction(nonTerminal(SORT),
                                             terminal(String2EKoreKString("\":" +String token2String(SORT) +String "\""))),
                                 kAttributesDeclaration(consAttrList(
                                    tagContent(#token("klabel","LowerName"),
                                               String2TagContents("SemanticCastTo" +String token2String(SORT))),dotAttrList(.KList)))))))
          , SORTS (.Set => SetItem(SORT)))
     requires notBool SORT in SORTS
  rule #addCasts2(Prds, _) => Prds [owise]

  // subsorts: K ::= Sort, Sort ::= KBott
  syntax Set ::= "#addSubsorts" "(" Set ")" [function]
  syntax Set ::= "#addSubsorts2" "(" Set "," Set ")" [function]
  rule #addSubsorts(Prds) => #addSubsorts2(Prds, noLatticeSortsInit)
  rule #addSubsorts2(
          SetItem(kSyntaxProduction(SORT, PROD))
          _:Set
          (.Set => 
              SetItem(kSyntaxProduction(String2UpperName("K"), kProductionWAttr(nonTerminal(SORT), noAtt)))
              SetItem(kSyntaxProduction(SORT, kProductionWAttr(nonTerminal(String2UpperName("KBott")), noAtt))))
          , SORTS (.Set => SetItem(SORT)))
     requires notBool SORT in SORTS
  rule #addSubsorts2(Prds, _) => Prds [owise]

endmodule






module PARSE-OUTER
  imports KINK-CONFIGURATION
  imports PARSER-UTIL

  // TODO: remove: #writeStringToFile, #doSystem, #doSystemGetOutput, #doParseAST
  syntax KItem ::= "#parseOuter"
  rule <k> PGM:Any ~> #parseOuter => parseOuter(tokenToString(PGM)) ... </k>
endmodule






module PARSE-PROGRAM
  imports KINK-CONFIGURATION
  imports K-PRODUCTION-ABSTRACT
  imports EKORE-KSTRING-ABSTRACT
  imports KORE-HELPERS
  imports STRING
  imports FILE-UTIL
  imports PARSER-UTIL
  imports META-ACCESSORS

  syntax KItem ::= "#parseProgramPath" "(" String ")" // Program Filename
                 | "#parseProgram" "(" IOString ")" // Program content
                 | "#collectPgmGrammar"
  rule <k> #parseProgramPath(PGM_FILENAME) => #parseProgram(readFile(PGM_FILENAME)) ... </k>

  rule <k> #parseProgram(PGM)
        => parseWithProductions(GRAMMAR, "Pgm", PGM)
           ...
       </k>
       <prgGrammar> GRAMMAR </prgGrammar>
     requires GRAMMAR =/=K .Set

  rule <k> #collectPgmGrammar ... </k>
       <name> MName </name>
       <prgGrammar> .Set => #getAllProds(MName) </prgGrammar>
    requires findString(tokenToString(MName), "-SYNTAX", 0) =/=Int -1
  rule <k> #collectPgmGrammar => .K ... </k>
       <s> #STUCK() => .K ... </s>
endmodule






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
  imports META-ACCESSORS
  imports PARSER-GEN-HELPERS

  syntax KItem ::= "#parseConfigBubbles"
                 | "#createConfigGrammar"

  // create config grammar in modules where we find configs as bubbles
  rule <k> #createConfigGrammar ... </k> 
       <name> MName </name>
       <decl> kConfiguration(noAttrsB(_:Bubble)) </decl>
       <configGrammar> .Set => #addSubsorts(#addCasts(#getAllProds(MName) #getAllProds(#token("CONFIG-INNER", "UpperName")))) </configGrammar>

  //rule <k> #createConfigGrammar => .K ... </k>
   //    <s> #STUCK() => .K ... </s>

  // actually parsing the configuration once we have the grammar
  rule <k> #parseConfigBubbles ... </k>
       <decl> kConfiguration(noAttrsB(C:Bubble)) => kConfiguration(noAttrsP({parseWithProductions(GRAMMAR, "K", tokenToString(C))}:>Pattern)) </decl>
       <configGrammar> GRAMMAR </configGrammar>
     requires GRAMMAR =/=K .Set
  
  rule <k> #parseConfigBubbles => .K ... </k>
       <s> #STUCK() => .K ... </s>

  
  // collect config info - destructure the configuration and populate <configInfo>
  // with \dv key -> type (CellInfo or KConfigVar)
  syntax KItem ::= "#extractConfigInfo"
  syntax KItem ::= collectCellName(Patterns)
  rule <k> #extractConfigInfo => collectCellName(P, .Patterns) ~> #extractConfigInfo ... </k>
       <decl> kConfiguration(noAttrsP(P)) </decl>
       <collected> Configs => Configs SetItem(P) </collected>
     requires notBool P in Configs

  rule <k> collectCellName( _ { _ } (A), .Patterns) => collectCellName(A) ... </k>
  rule <k> collectCellName(A, B) => collectCellName(A, .Patterns) ~> collectCellName(B) ... </k>
    requires B =/=K .Patterns
  rule <k> collectCellName( .Patterns ) => .K ... </k>

  syntax String ::= token2String(KoreString) [function, functional, hook(STRING.token2string)]
  rule <k> collectCellName(\dv { Srt { .Sorts } } ( CellName ), .Patterns) => .K ... </k>
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
  imports DISAMBIGUATE

  // parse rule bubbles
  syntax KItem ::= "#parseRuleBubbles"
                 | "#createRuleGrammar"

  rule <k> #createRuleGrammar ... </k> // create rule grammar
       <name> MName </name>
       <decl> kRule(noAttrsB(_:Bubble)) </decl>
       <ruleGrammar> .Set => #addRuleCells(#addSubsorts(#addCasts(#getAllProds(MName) #getAllProds(#token("RULE-INNER", "UpperName"))))) </ruleGrammar>
  rule <k> #createRuleGrammar ... </k> // create rule grammar for rules with attributes
       <name> MName </name>
       <decl> kRule(attrsB(_:Bubble, _)) </decl>
       <ruleGrammar> .Set => #addRuleCells(#addSubsorts(#addCasts(#getAllProds(MName) #getAllProds(#token("RULE-INNER", "UpperName"))))) </ruleGrammar>

  rule <k> #createRuleGrammar => .K ... </k>
       <s> #STUCK() => .K ... </s>

  rule <k> #parseRuleBubbles ... </k>
       <decl> kRule(noAttrsB(C:Bubble)) => kRule(noAttrsP(disambiguate({parseWithProductions(GRAMMAR, "RuleContent", tokenToString(C))}:>Pattern, GRAMMAR))) </decl>
       <ruleGrammar> GRAMMAR </ruleGrammar>
     requires GRAMMAR =/=K .Set
  rule <k> #parseRuleBubbles ... </k>
       <decl> kRule(attrsB(C:Bubble, At)) => kRule(attrsP({parseWithProductions(GRAMMAR, "RuleContent", tokenToString(C))}:>Pattern, At)) </decl>
       <ruleGrammar> GRAMMAR </ruleGrammar>
     requires GRAMMAR =/=K .Set

  rule <k> #parseRuleBubbles => .K ... </k>
       <s> #STUCK() => .K ... </s>

  // add rule cells
  syntax Set ::= "#addRuleCells" "(" Set ")" [function]
  syntax Set ::= "#addRuleCells2" "(" Set "," Set ")" [function]
  rule #addRuleCells(Prds) => #addRuleCells2(Prds, .Set)
  rule [[ #addRuleCells2(
        Prds:Set
        (.Set => SetItem(
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
                   tagSimple(#token("cell","LowerName")), dotAttrList(.KList)))))))))
        , Cells (.Set => SetItem(CellName)))
        ]]
       <cellName> CellName |-> "CellName" ... </cellName>
     requires notBool CellName in Cells
  rule #addRuleCells2(Prods, _) => Prods [owise]

endmodule






module PARSE-TO-EKORE
  imports EKORE-ABSTRACT
  imports KINK-CONFIGURATION
  imports PARSER-UTIL

  syntax KItem ::= "#parseToEKore"
  rule <k> PGM:Any ~> #parseToEKore => parseEKore(tokenToString(PGM)) ... </k>
endmodule


