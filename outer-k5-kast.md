```k
// Copyright (c) 2015-2018 K Team. All Rights Reserved.
// written by Radu Mereuta
// This grammar is supposed to accept as input a full K definition
// which includes modules, syntax declarations and rules as kast.

module TOKENS
  syntax UpperName
  syntax LowerName
  syntax Numbers
endmodule

module TOKENS-SYNTAX
  syntax UpperName ::= r"[A-Z][A-Za-z\\-0-9]*" [token]
  syntax LowerName ::= r"[a-z][A-Za-z\\-0-9]*" [token] | "left" [token] // I have no idea why I need to redeclare 'left', but it gives a parsing error otherwise
  syntax Numbers   ::= r"[\\+-]?[0-9]+"        [token]
endmodule

module ATTRIBUTES
  imports KSTRING
  imports TOKENS

  syntax TagContent ::= UpperName [token] | LowerName [token] | Numbers [token]
  syntax TagContents ::= NeList{TagContent,""} [klabel(tagContents), token]
  syntax KEY ::= LowerName [token]
  syntax Attr ::= KEY                     [klabel(tagSimple)]
                | KEY "(" TagContents ")" [klabel(tagContent)]
                | KEY "(" KString ")"     [klabel(tagString)]
endmodule

module SYNTAX-DECL
  imports KSTRING
  imports ATTRIBUTES

  syntax KDefinition   ::= KRequireList KModuleList [klabel(kDefinition)]

  syntax KRequire      ::= "require" KString [klabel(kRequire)]

  syntax KRequireList  ::= List{KRequire, ""}  [klabel(KRequireList)]

  syntax KModule       ::= "module" KModuleName OptionalAttributes
                                    KImportList
                                    KSentenceList
                           "endmodule"
                               [klabel(kModule)]
  syntax KModuleList   ::= List{KModule, ""}  [klabel(kModuleList)]

  syntax KImport       ::= "imports" KModuleName [klabel(kImport)]

  syntax KImportList   ::= List{KImport, ""}  [klabel(kImportList)]
  syntax KSentenceList ::= List{KSentence, ""}  [klabel(kSentenceList)]

  syntax KSentence ::= "syntax" KSort OptionalAttributes [klabel(kSyntaxSort)]
                     | "syntax" KSort "::=" PrioritySeqBlock [klabel(kSyntaxProduction)]
                     | "syntax" "priority"   KPrioritySeq OptionalAttributes [klabel(kSyntaxPriority)]
                     | "syntax" "priorities" KPrioritySeq OptionalAttributes [klabel(kSyntaxPriorities)]
                     | "syntax" "left" KNeTagSet OptionalAttributes [klabel(kSyntaxLeft)]
                     | "syntax" "right" KNeTagSet OptionalAttributes [klabel(kSyntaxRight)]
                     | "syntax" "non-assoc" KNeTagSet OptionalAttributes [klabel(kSyntaxNonAssoc)]

  syntax KPrioritySeq ::= KPrioritySeq ">" KNeTagSet   [klabel(kPrioritySeq)]
                        | KNeTagSet
  syntax KNeTagSet    ::= NeList{Tag, ""} [klabel(kTagSet)]

  syntax Tag ::= UpperName [token] | LowerName [token]

  syntax KProduction ::= KProductionItem
                       | KProduction KProductionItem [klabel(kProduction), unit(emptyKProduction)]
  syntax KProductionItem ::= KSort       [klabel(nonTerminal)]
                           | KString     [klabel(terminal)]
                           | "r" KString [klabel(regexTerminal)]
                           | "NeList" "{" KSort "," KString "}" [klabel(neListProd)]
                           |   "List" "{" KSort "," KString "}" [klabel(listProd)]
  syntax PrioritySeqBlock ::= PrioritySeqBlock ">" AssocAttribute ProdBlock [klabel(prioritySeqBlock)]
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

  syntax KSentence ::= "configuration" Contents [klabel(kConfiguration)]
                     | "rule"    Contents [klabel(kRule)]
                     | "context" Contents [klabel(kContext)]

  syntax Pattern
  syntax Contents ::= Pattern                        [klabel(noAttrs)]
                    | Pattern KAttributesDeclaration [klabel(attrs), prefer]

  syntax KModuleName ::= UpperName [token]
  syntax KSort       ::= UpperName [token]
endmodule

module KAST2
  imports TOKENS-SYNTAX
  imports SYNTAX-DECL
  syntax K2      ::= KLabel2 "(" KList2 ")" [klabel(kapp)]
                   | VarName ":" KSort [klabel(cast)]
                   | VarName
                   | "#token" "(" KString "," KString ")" [klabel(ktoken)]
                   | "#klabel" "(" KLabel2 ")" [klabel(wrappedklabel)]
                   | ".K"  [klabel(emptyK)]
                   > K2 "~>" K2 [left, klabel(ksequence)]
                   > K2 "=>" K2 [non-assoc, klabel(krewrite)]
  syntax KLabel2 ::= LowerName [token]
                   | r"`(\\\\`|\\\\\\\\|[^`\\\\\\n\\r])+`" [token]
  syntax KList2  ::= KList2 "," KList2 [left, klabel(klist)]
                   | K2
                   | ".KList" [klabel(emptyKList)]
  syntax VarName ::= UpperName [token]
                   | r"(\\$)([A-Z][A-Za-z\\-0-9]*)" [token]
endmodule

module OUTER-K5-KAST-SYNTAX
  imports SYNTAX-DECL
  imports TOKENS-SYNTAX
  imports KAST2
  syntax Pattern ::= K2
                   | K2 "requires" K2 [klabel(requiresClause)]
  syntax AssocAttribute     ::= "" [klabel(noAttribute)]
  syntax OptionalAttributes ::= "" [klabel(noKAttributesDeclaration)]
endmodule

module OUTER-K5-KAST
  imports SYNTAX-DECL
  imports KAST
  syntax AssocAttribute     ::= "noAssoc" [klabel(noAttribute)]
  syntax OptionalAttributes ::= "noAtt"   [klabel(noKAttributesDeclaration)]

//  configuration <k> $PGM:KDefinition </k>

endmodule
```
