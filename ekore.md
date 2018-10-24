This grammar is supposed to accept as input a full K definition
which includes modules, syntax declarations and rules as kast.

```k
requires "kore.k"

module ATTRIBUTES
  imports KSTRING
  imports TOKENS

  syntax TagContent ::= UpperName | LowerName | Numbers
  syntax TagContents ::= NeList{TagContent,""} [klabel(tagContents)]
  syntax KEY ::= LowerName
  syntax Attr ::= KEY                     [klabel(tagSimple)]
                | KEY "(" TagContents ")" [klabel(tagContent)]
                | KEY "(" KString ")"     [klabel(tagString)]
endmodule

module K-DEFINITION
  imports EKORE1-DECLARATIONS

  syntax KDefinition   ::= KRequireList KModuleList [klabel(kDefinition), format(%1%n%n%2)]

  syntax KRequire      ::= "require" KString [klabel(kRequire)]
  syntax KRequireList  ::= List{KRequire, ""}  [klabel(KRequireList), format(%1%2%n%3)]

  syntax KModule       ::= "module" KModuleName OptionalAttributes
                                    KImportList
                                    Declarations
                           "endmodule"
                               [klabel(kModule), format(%1 %2 %3%i%n%4%n%5%n%d%6)]
  syntax KModuleList   ::= List{KModule, ""}  [klabel(kModuleList), format(%1%2%n%n%3)]

endmodule

module EKORE1-DECLARATIONS
  imports KSTRING
  imports ATTRIBUTES
  imports KORE-COMMON

  syntax Declaration ::= "syntax" KSort OptionalAttributes [klabel(kSyntaxSort)]
                       | "syntax" KSort "::=" PrioritySeqBlock [klabel(kSyntaxProduction), format(%1 %2 %3%i%n%4%d)]
                       | "syntax" "priority"   KPrioritySeq OptionalAttributes [klabel(kSyntaxPriority)]
                       | "syntax" "priorities" KPrioritySeq OptionalAttributes [klabel(kSyntaxPriorities)]
                       | "syntax" "left" KNeTagSet OptionalAttributes [klabel(kSyntaxLeft)]
                       | "syntax" "right" KNeTagSet OptionalAttributes [klabel(kSyntaxRight)]
                       | "syntax" "non-assoc" KNeTagSet OptionalAttributes [klabel(kSyntaxNonAssoc)]

  syntax KPrioritySeq ::= KPrioritySeq ">" KNeTagSet   [klabel(kPrioritySeq)]
                        | KNeTagSet
  syntax KNeTagSet    ::= NeList{Tag, ""} [klabel(kTagSet)]

  syntax Tag ::= UpperName | LowerName

  syntax KProduction ::= KProductionItem
                       | KProduction KProductionItem [klabel(kProduction), unit(emptyKProduction)]
  syntax KProductionItem ::= KSort       [klabel(nonTerminal)]
                           | KString     [klabel(terminal)]
                           | "r" KString [klabel(regexTerminal)]
                           | "NeList" "{" KSort "," KString "}" [klabel(neListProd)]
                           |   "List" "{" KSort "," KString "}" [klabel(listProd)]
  syntax PrioritySeqBlock ::= PrioritySeqBlock ">" AssocAttribute ProdBlock [klabel(prioritySeqBlock), format(  %1%n%2 %3%4)]
                            | ProdBlock
  syntax AssocAttribute ::= "left:"      [klabel(leftAttribute)]
                          | "right:"     [klabel(rightAttribute)]
                          | "non-assoc:" [klabel(nonAssocAttribute)]
  syntax ProdBlock ::= ProdBlock "|" KProductionWAttr [klabel(prodBlock)]
                     | KProductionWAttr
  syntax KProductionWAttr ::= KProduction OptionalAttributes [klabel(kProductionWAttr)]
                            | Tag "(" KSortList ")" OptionalAttributes [klabel(kFuncProductionWAttr)]
                            |     "(" KSortList ")" OptionalAttributes [klabel(kTupleProductionWAttr)]
  syntax KSortList ::= KSortList "," KSort [klabel(kSortList)]
                     | KSort

  syntax OptionalAttributes ::= KAttributesDeclaration

  syntax KAttributesDeclaration ::= "[" AttrList "]" [klabel(kAttributesDeclaration)]
  syntax AttrList ::= NeList{Attr, ","} [klabel(kAttributesList)]

  syntax Declaration ::= "configuration" Contents [klabel(kConfiguration)]
                       | "rule"    Contents [klabel(kRule)]
                       | "context" Contents [klabel(kContext)]


  syntax Declaration   ::= KImport
  syntax KImport       ::= "imports" KModuleName [klabel(kImport)]
  syntax KImportList   ::= List{KImport, ""}  [klabel(kImportList), format(%1%2%n%3)]

  syntax Contents ::= Pattern                        [klabel(noAttrs)]
                    | Pattern KAttributesDeclaration [klabel(attrs), prefer]

  syntax KModuleName ::= UpperName [token]
  syntax KSort       ::= UpperName [token]
endmodule

module EKORE0-DECLARATIONS
  imports TOKENS-SYNTAX
  imports EKORE1-DECLARATIONS
  syntax Variable ::= VarName ":" KSort [klabel(cast)]
                    | VarName

  syntax Pattern  ::= "#token" "(" KString "," KString ")" [klabel(ktoken)]
                    | "#klabel" "(" KLabel2 ")" [klabel(wrappedklabel)]
                    | Pattern "requires" Pattern [klabel(requiresClause)]
                    // TODO: Can we enforce disallowing nested rewrites at syntax?
                    > Pattern "~>" Pattern [left, klabel(ksequence)]
                    > Pattern "=>" Pattern [non-assoc, klabel(krewrite)]
  syntax KLabel2 ::= LowerName [token]
                   | r"`(\\\\`|\\\\\\\\|[^`\\\\\\n\\r])+`" [token]
  syntax Symbol  ::= KLabel2
  syntax VarName ::= UpperName [token]
                   | r"(\\$)([A-Z][A-Za-z\\-0-9]*)" [token]
endmodule

module EKORE-COMMON
  imports K-DEFINITION
  imports EKORE1-DECLARATIONS
endmodule

module EKORE-SYNTAX
  imports EKORE-COMMON
  imports TOKENS-SYNTAX
  imports EKORE0-DECLARATIONS
  syntax AssocAttribute     ::= "" [klabel(noAttribute)]
  syntax OptionalAttributes ::= "" [klabel(noKAttributesDeclaration)]
endmodule

module EKORE
  imports EKORE-COMMON
  imports KAST
  syntax AssocAttribute     ::= "noAssoc" [klabel(noAttribute)]
  syntax OptionalAttributes ::= "noAtt"   [klabel(noKAttributesDeclaration)]
endmodule
```
