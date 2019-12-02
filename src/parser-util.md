Parsing utils

```k
module PARSER-UTIL
  imports FILE-UTIL
  imports K-REFLECTION
  imports EKORE-ABSTRACT
  imports KINK-CONFIGURATION

  syntax String ::= tokenToString(K) [function, functional, hook(STRING.token2string)]

  syntax KItem ::= parseOuter(String) [function]
  rule [[ parseOuter(S)
       => doParseKAST(parseHelper( module = "OUTER-SYNTAX"
                               , grammarFile = DEPLOY_DIR +String "/src/ekore.k"
                               , start = "Definition"
                               , input = S
                               , output = "kast"
                   )           )
       ]]
       <kinkDeployedDir> DEPLOY_DIR </kinkDeployedDir>

  syntax KItem ::= parseEKore(String) [function]
  rule [[ parseEKore(S)
       => doParseKAST(parseHelper( module = "EKORE-SYNTAX"
                             , grammarFile = DEPLOY_DIR +String "/src/ekore.k"
                             , start = "Definition"
                             , input = S
                             , output = "kast"
                 )           )
       ]]
       <kinkDeployedDir> DEPLOY_DIR </kinkDeployedDir>

  syntax KItem ::= parseSymbolName(String) [function]
  rule [[ parseSymbolName(S)
       => doParseKAST(parseHelper( module = "EKORE-SYNTAX"
                                 , grammarFile = DEPLOY_DIR +String "/src/ekore.k"
                                 , start = "SymbolName"
                                 , input = S
                                 , output = "kast"
                     )           )
       ]]
       <kinkDeployedDir> DEPLOY_DIR </kinkDeployedDir>

  syntax KItem ::= doParseKAST(K) [function]
  rule doParseKAST(S:String) => #parseKAST(S)

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
                   , start = START, inputFile = saveToTempFile(INPUT, "k-in-kXXXXXX")
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

  syntax KItem ::= parseWithProductions( Set   /* list of prods */
                                       , String /* start symbol */
                                       , String /* input */
                                       ) [function]
  rule [[ parseWithProductions(GRAMMAR, START, INPUT)
       => doParseKAST(parseHelper( module = "KORE-SYNTAX"
                                 , grammarFile = DEPLOY_DIR +String "/src/kore.k"
                                 , start = "Pattern"
                                 , input = parseHelper( module = "LANGUAGE-GRAMMAR"
                                                      , grammarFile = saveToTempFile("module LANGUAGE-GRAMMAR\n"
                                                                             +String grammarToString(GRAMMAR)
                                                                             +String "endmodule"
                                                                                    , "")
                                                      , start = START
                                                      , input = INPUT
                                                      , output = "kore"
                                                      )
                                 , output = "kast"
                     )           )
       ]]
       <kinkDeployedDir> DEPLOY_DIR </kinkDeployedDir>

  syntax String ::= grammarToString(Set) [function]
  rule grammarToString(.Set) => ""
  rule grammarToString(SetItem(kSyntaxProduction(S, kProductionWAttr(P, ATTRS))) DECLS)
    => "syntax " +String tokenToString(S) +String " ::= "
                 +String KProductionToString(P) +String " "
                 +String OptionalAttributesToString(ATTRS)
       +String "\n"
       +String grammarToString(DECLS)

  syntax String ::= KSortListToString(KSortList) [function]
  rule KSortListToString(S:KSort) => tokenToString(S)
  rule KSortListToString(Ss, S) => KSortListToString(Ss) +String "," +String tokenToString(S)

  syntax String ::= KProductionToString(KProduction) [function]
  rule KProductionToString(PI:KProductionItem)
    => KProductionItemToString(PI)
  rule KProductionToString(kProduction(PI, PIs))
    => KProductionItemToString(PI) +String " " +String KProductionToString(PIs)
  rule KProductionToString(TAG:Tag(KSORTLIST:KSortList))
    => tokenToString(TAG) +String "(" +String KSortListToString(KSORTLIST) +String ")"

  syntax String ::= KProductionItemToString(KProductionItem) [function]
  rule KProductionItemToString(nonTerminal(N)) => tokenToString(N)
  rule KProductionItemToString(terminal(T))    => tokenToString(T)
  rule KProductionItemToString(regexTerminal(R)) => "r" +String tokenToString(R)

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
    => tokenToString(KEY)
  rule AttrToString(KEY:KEY(CONTENTS:TagContents))
    => tokenToString(KEY) +String "(" +String tokenToString(CONTENTS) +String ")"

  syntax String ::= TagContentsToString(TagContents) [function]
  rule TagContentsToString(tagContents(TC, TCs))
    => tokenToString(TC) +String " " +String TagContentsToString(TCs)
  rule TagContentsToString(.tagContents)
    => ""
endmodule
```
