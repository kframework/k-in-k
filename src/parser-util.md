Parsing utils

```k
module PARSER-UTIL
  imports FILE-UTIL
  imports META
  imports EKORE-ABSTRACT

  syntax KItem ::= parseOuter(String) [function, impure]
  rule parseOuter(S)
    => doParseAST(parseHelper( module = "OUTER-SYNTAX"
                             , grammarFile = ".build/src/ekore.k" 
                             , start = "Definition"
                             , input = S
                             , output = "kast"
                 )           )
  syntax KItem ::= parseEKore     (String) [function, impure]
  rule parseEKore(S)
    => doParseAST(parseHelper( module = "EKORE-SYNTAX"
                             , grammarFile = ".build/src/ekore.k" 
                             , start = "Definition"
                             , input = S
                             , output = "kast"
                 )           )

  syntax KItem ::= doParseAST(K) [function]
  rule doParseAST(S:String) => #parseAST(S)

  // TODO: Deal with temp file removal
  syntax KItem ::= "parseHelper"  "(" "module" "=" String
                                  "," "grammarFile" "=" IOString
                                  "," "start" "=" String
                                  "," "input" "=" KItem
                                  "," "output" "=" String
                                  ")" [function, impure]
                 | "parseHelper1" "(" "module" "=" String
                                  "," "grammarFile" "=" IOString
                                  "," "start" "=" String
                                  "," "inputFile" "=" IOString
                                  "," "output" "=" String
                                  ")" [function, impure]
                 | "parseHelper2" "(" KItem ")" [function]
  rule parseHelper(module = MOD, grammarFile = GRAMMAR, start = START, input = INPUT:String, output = OUTPUT)
    => parseHelper1( module = MOD, grammarFile = GRAMMAR
                   , start = START, inputFile = saveToTempFile(INPUT, "", "")
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

  syntax KItem ::= parseWithProductions( Declarations   /* list of prods */
                                       , String /* start symbol */
                                       , String /* input */
                                       ) // [function, impure]
  rule parseWithProductions(GRAMMAR, START, INPUT)
    => doParseAST(parseHelper( module = "KORE-SYNTAX"
                             , grammarFile = ".build/kore.k"
                             , start = "Pattern"
                             , input = parseHelper( module = "LANGUAGE-GRAMMAR"
                                                  , grammarFile = saveToTempFile("module LANGUAGE-GRAMMAR\n"
                                                                         +String grammarToString(GRAMMAR)
                                                                         +String "endmodule"
                                                                                , "", ""
                                                                                )
                                                  , start = START
                                                  , input = INPUT
                                                  , output = "kore"
                                                  )
                             , output = "kast"
                 )           )
  syntax String ::= grammarToString(Declarations) [function]
  rule grammarToString(.Declarations)
    => ""
  rule grammarToString(kSyntaxProduction(S, kProductionWAttr(P, ATTRS)) DECLS)
    => "syntax " +String tokenToString(S) +String " ::= "
                 +String KProductionToString(P) +String " "
                 +String OptionalAttributesToString(ATTRS)
       +String "\n"
       +String grammarToString(DECLS)
  rule grammarToString( kSyntaxProduction(S, TAG:Tag(KSORTLIST:KSortList) ATTRS)
                        DECLS
                      )
    => "syntax " +String tokenToString(S) +String " ::= "
                 +String tokenToString(TAG)
                 +String "(" +String KSortListToString(KSORTLIST) +String ")" +String " "
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
    => KProductionItemToString(PI) +String "\n" +String KProductionToString(PIs)

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

  syntax String ::= AttrToString(Attr) [function]
  rule AttrToString(tagSimple(KEY))
    => tokenToString(KEY)
  rule AttrToString(KEY:KEY(CONTENTS:TagContents))
    => tokenToString(KEY) +String "(" +String tokenToString(CONTENTS) +String ")"
  rule AttrToString(KEY:KEY(CONTENTS:EKoreKString))
    => tokenToString(KEY) +String "(" +String tokenToString(CONTENTS) +String ")"

  syntax String ::= TagContentsToString(TagContents) [function]
  rule TagContentsToString(tagContents(TC, TCs))
    => tokenToString(TC) +String " " +String TagContentsToString(TCs)
  rule TagContentsToString(.TagContents)
    => ""
endmodule
```
