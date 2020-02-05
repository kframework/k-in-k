Parsing utils

```k
module STRING-UTIL
  imports STRING-SYNTAX
  syntax {S} String ::= tokenToString(S) [function, functional, hook(STRING.token2string)]
endmodule

module PARSER-UTIL
  imports FILE-UTIL
  imports K-REFLECTION
  imports EKORE-ABSTRACT
  imports KINK-CONFIGURATION
  imports STRING-UTIL


  syntax Definition ::= parseOuter(String) [function]
  // TODO: right now K doesn't support parametric functions except for hooks
  // when this is available, the syntax should look like
  // syntax {S} S ::= doParseKAST(K) [function]
  // rule doParseKAST(S:String) => #parseKORE(S)
  syntax Definition ::= doParseDefinition(K) [function]
  rule doParseDefinition(S:String) => #parseKORE(S)
  rule [[ parseOuter(S)
       => doParseDefinition(parseHelper( module = "OUTER-SYNTAX"
                               , grammarFile = DEPLOY_DIR +String "/src/ekore.k"
                               , start = "Definition"
                               , input = S
                               , output = "kore"
                   )           )
       ]]
       <kinkDeployedDir> DEPLOY_DIR </kinkDeployedDir>

  syntax Pattern ::= parseEKore(String) [function]
  syntax Pattern ::= doParsePattern(K) [function]
  rule doParsePattern(S:String) => #parseKORE(S)
  rule [[ parseEKore(S)
       => doParsePattern(parseHelper( module = "EKORE-SYNTAX"
                             , grammarFile = DEPLOY_DIR +String "/src/ekore.k"
                             , start = "Definition"
                             , input = S
                             , output = "kore"
                 )           )
       ]]
       <kinkDeployedDir> DEPLOY_DIR </kinkDeployedDir>

  syntax SymbolName ::= parseSymbolName(String) [function]
  syntax SymbolName ::= doParseSymbolName(K) [function]
  rule doParseSymbolName(S:String) => #parseKORE(S)
  rule [[ parseSymbolName(S)
       => doParseSymbolName(parseHelper( module = "EKORE-SYNTAX"
                                 , grammarFile = DEPLOY_DIR +String "/src/ekore.k"
                                 , start = "SymbolName"
                                 , input = S
                                 , output = "kore"
                     )           )
       ]]
       <kinkDeployedDir> DEPLOY_DIR </kinkDeployedDir>

  // TODO: Deal with temp file removal
  syntax KItem ::= "parseHelper"  "(" "module" "=" String
                                  "," "grammarFile" "=" IOString
                                  "," "start" "=" String
                                  "," "input" "=" KItem
                                  "," "output" "=" String
                                  ")" [function]
                 | "parseHelper1" "(" "module" "=" String
                                  "," "grammarFile" "=" IOString
                                  "," "start" "=" String
                                  "," "inputFile" "=" IOString
                                  "," "output" "=" String
                                  ")" [function]
                 | "parseHelper2" "(" KItem ")" [function]
  rule parseHelper(module = MOD, grammarFile = GRAMMAR, start = START, input = INPUT:String, output = OUTPUT)
    => parseHelper1( module = MOD, grammarFile = GRAMMAR
                   , start = START, inputFile = saveToTempFile(INPUT, "/tmp/parseHelperXXXXXX")
                   , output = OUTPUT
                   )
  rule parseHelper1(module = _, grammarFile = _, start = _, inputFile = E:IOError, output = _)
    => E
  rule parseHelper1(module = MOD, grammarFile = GRAMMAR, start = START, inputFile = INPUTFILE, output = OUTPUT)
    => parseHelper2(#system("k-light2k5.sh --output " +String OUTPUT +String
                                         " --module " +String MOD +String
                                         " " +String GRAMMAR +String
                                         " " +String START +String
                                         " " +String INPUTFILE
                   )       )
  rule parseHelper2(#systemResult(0, STDOUT, _))
    => STDOUT

  syntax Pattern ::= parseWithProductions( Set   /* list of prods */
                                       , String /* start symbol */
                                       , String /* input */
                                       ) [function]
  rule [[ parseWithProductions(GRAMMAR, START, INPUT)
       => doParsePattern(parseHelper( module = "KORE-SYNTAX"
                                 , grammarFile = DEPLOY_DIR +String "/src/kore.k"
                                 , start = "Pattern"
                                 , input = parseHelper( module = "LANGUAGE-GRAMMAR"
                                                      , grammarFile = saveToTempFile("module LANGUAGE-GRAMMAR\n"
                                                                             +String grammarToString(GRAMMAR)
                                                                             +String "endmodule"
                                                                                    , "/tmp/parseKASTXXXXXXXX")
                                                      , start = START
                                                      , input = INPUT
                                                      , output = "kore"
                                                      )
                                 , output = "kore"
                     )           )
       ]]
       <kinkDeployedDir> DEPLOY_DIR </kinkDeployedDir>

  syntax String ::= grammarToString(Set) [function]
  rule grammarToString(.Set) => ""
  rule grammarToString(SetItem(kSyntaxProduction(S, kProductionWAttr(P, ATTRS))) DECLS)
    => "syntax " +String tokenToString(S:UpperName) +String " ::= "
                 +String KProductionToString(P) +String " "
                 +String OptionalAttributesToString(ATTRS)
       +String "\n"
       +String grammarToString(DECLS)

  syntax String ::= KSortListToString(KSortList) [function]
  rule KSortListToString(S:UpperName) => tokenToString(S)
  rule KSortListToString(kSortList(Ss, S)) => KSortListToString(Ss) +String "," +String tokenToString(S:UpperName)

  syntax String ::= KProductionToString(KProduction) [function]
  rule KProductionToString(PI:KProductionItem)
    => KProductionItemToString(PI)
  rule KProductionToString(kProduction(PI, PIs))
    => KProductionItemToString(PI) +String " " +String KProductionToString(PIs)
  //rule KProductionToString(TAG:Tag(KSORTLIST:KSortList))
  //  => tokenToString(TAG) +String "(" +String KSortListToString(KSORTLIST) +String ")"

  syntax String ::= KProductionItemToString(KProductionItem) [function]
  rule KProductionItemToString(nonTerminal(N)) => tokenToString(N:UpperName)
  rule KProductionItemToString(terminal(T))    => tokenToString(T:EKoreKString)
  rule KProductionItemToString(regexTerminal(R)) => "r" +String tokenToString(R:EKoreKString)

  syntax String ::= OptionalAttributesToString(OptionalAttributes) [function]
  rule OptionalAttributesToString(noAtt) => ""
  rule OptionalAttributesToString([ ATTRLIST ])
    => "[" +String AttrListToString(ATTRLIST) +String "]"

  syntax String ::= AttrListToString(AttrList) [function]
  rule AttrListToString(.AttrList)       => "dummy"
  rule AttrListToString(ATTR, .AttrList) => AttrToString(ATTR)
  rule AttrListToString(ATTR, ATTRs)     => AttrToString(ATTR) +String "," +String AttrListToString(ATTRs)
    requires notBool ATTRs ==K .AttrList

  syntax String ::= AttrToString(Attr) [function]
  rule AttrToString(tagSimple(KEY))
    => tokenToString(KEY:LowerName)
  rule AttrToString(tagContent(KEY, CONTENTS))
    => tokenToString(KEY:LowerName) +String "(" +String tokenToString(CONTENTS:TagContents) +String ")"
    requires CONTENTS =/=K .tagContents
  rule AttrToString(tagContent(KEY, CONTENTS))
    => tokenToString(KEY:LowerName)
    requires CONTENTS ==K .tagContents

endmodule
```
