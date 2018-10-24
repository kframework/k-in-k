In this file, we extend the Kore syntax to include K Frontend syntax. We aim for
a telescopic set of syntaxes, each extending the next, the smallest being Kore,
and the largest, the K Frontend syntax. We build each of these subsets out of
smaller building blocks that we call "extensions".

```k
requires "kore.k"
```

Writing rules over concrete K syntax leads to ambiguities, since the parser must
disambiguate between the outer syntax and the inner syntax which are for the
most part identical. To work around this issue, we define contstructs that are
likely to give rise to ambiguities twice: once with the concrete syntax for
parsing (suffixed with `-SYNTAX`), and a second time with abstract syntax for
writing rules over (unsuffixed). We may also define a third module (suffixed
`-COMMON`) with code that these two modules can share.

EKore 1
=======

EKORE1 extends KORE with frontend syntax for `syntax`, `rule`s,
`configuration` and `context`s. Rules do not allow for concrete language syntax
or even kast syntax, but only for the Kore notation for referencing symbols.

```k
module EKORE1-DECLARATIONS-SYNTAX
  imports KSTRING
  imports ATTRIBUTES-SYNTAX
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
                          | ""           [klabel(noAttribute)]
  syntax ProdBlock ::= ProdBlock "|" KProductionWAttr [klabel(prodBlock)]
                     | KProductionWAttr
  syntax KProductionWAttr ::= KProduction OptionalAttributes [klabel(kProductionWAttr)]
                            | Tag "(" KSortList ")" OptionalAttributes [klabel(kFuncProductionWAttr)]
                            |     "(" KSortList ")" OptionalAttributes [klabel(kTupleProductionWAttr)]
  syntax KSortList ::= KSortList "," KSort [klabel(kSortList)]
                     | KSort

  syntax OptionalAttributes ::= KAttributesDeclaration
                              | "" [klabel(noKAttributesDeclaration)]

  syntax KAttributesDeclaration ::= "[" AttrList "]" [klabel(kAttributesDeclaration)]
  syntax AttrList ::= NeList{Attr, ","} [klabel(kAttributesList)]

  syntax Declaration ::= "configuration" Contents [klabel(kConfiguration)]
                       | "rule"    Contents [klabel(kRule)]
                       | "context" Contents [klabel(kContext)]

  syntax KImport       ::= "imports" KModuleName [klabel(kImport)]
  syntax KImportList   ::= List{KImport, ""}  [klabel(kImportList), format(%1%2%n%3)]

  syntax Contents ::= Pattern                        [klabel(noAttrs)]
                    | Pattern KAttributesDeclaration [klabel(attrs), prefer]
endmodule

module EKORE1-DECLARATIONS
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
  syntax KProductionItem ::= nonTerminal(KSort)         [klabel(nonTerminal)]
                           | terminal(KString)          [klabel(terminal)]
                           | regexTerminal(KString)     [klabel(regexTerminal)]
                           | neListProd(KSort, KString) [klabel(neListProd)]
                           | listProd(KSort,KString)    [klabel(listProd)]
  syntax PrioritySeqBlock ::= PrioritySeqBlock ">" AssocAttribute ProdBlock [klabel(prioritySeqBlock), format(  %1%n%2 %3%4)]
                            | ProdBlock
  syntax AssocAttribute ::= "left:"      [klabel(leftAttribute)]
                          | "right:"     [klabel(rightAttribute)]
                          | "non-assoc:" [klabel(nonAssocAttribute)]
                          | "noAssoc" [klabel(noAttribute)]
  syntax ProdBlock ::= ProdBlock "|" KProductionWAttr [klabel(prodBlock)]
                     | KProductionWAttr
  syntax KProductionWAttr ::= KProduction OptionalAttributes [klabel(kProductionWAttr)]
                            | Tag "(" KSortList ")" OptionalAttributes [klabel(kFuncProductionWAttr)]
                            |     "(" KSortList ")" OptionalAttributes [klabel(kTupleProductionWAttr)]
  syntax KSortList ::= KSortList "," KSort [klabel(kSortList)]
                     | KSort

  syntax OptionalAttributes ::= KAttributesDeclaration
                              | "noAtt" [klabel(noKAttributesDeclaration)]

  syntax KAttributesDeclaration ::= "[" AttrList "]" [klabel(kAttributesDeclaration)]
  syntax AttrList ::= NeList{Attr, ","} [klabel(kAttributesList)]

  syntax Declaration ::= "configuration" Contents [klabel(kConfiguration)]
                       | "rule"    Contents [klabel(kRule)]
                       | "context" Contents [klabel(kContext)]

  syntax KImport       ::= "imports" KModuleName [klabel(kImport)]
  syntax KImportList   ::= List{KImport, ""}  [klabel(kImportList), format(%1%2%n%3)]

  syntax Contents ::= noAttrs(Pattern)                       [klabel(noAttrs)]
                    | attrs(Pattern, KAttributesDeclaration) [klabel(attrs), prefer]
endmodule


module ATTRIBUTES
  imports KSTRING
  imports TOKENS

  syntax TagContent ::= UpperName | LowerName | Numbers
  syntax TagContents ::= NeList{TagContent,""} [klabel(tagContents)]
  syntax KEY ::= LowerName
  syntax Attr ::= tagSimple(LowerName)    [klabel(tagSimple)]
                | KEY "(" TagContents ")" [klabel(tagContent)]
                | KEY "(" KString ")"     [klabel(tagString)]
endmodule

module ATTRIBUTES-SYNTAX
  imports KSTRING
  imports TOKENS-SYNTAX

  syntax TagContent ::= UpperName | LowerName | Numbers
  syntax TagContents ::= NeList{TagContent,""} [klabel(tagContents)]
  syntax KEY ::= LowerName
  syntax Attr ::= KEY                     [klabel(tagSimple)]
                | KEY "(" TagContents ")" [klabel(tagContent)]
                | KEY "(" KString ")"     [klabel(tagString)]
endmodule
```

EKore 0
=======

`EKORE0` extends `EKORE1` allowing the use of "backtick" kast syntax, `#token`,
rewrite and sequencing arrows.

```k
module EKORE0-DECLARATIONS
  imports TOKENS
  imports EKORE1-DECLARATIONS
  syntax Variable ::= cast(VarName, KSort) [klabel(cast)]
                    | VarName
  syntax Pattern  ::= ktoken(KString, KString)         [klabel(ktoken)]
                    | wrappedklabel(KLabel2)           [klabel(wrappedklabel)]
                    | requiresClause(Pattern, Pattern) [klabel(requiresClause)]
                    > ksequence(Pattern, Pattern)      [left, klabel(ksequence)]
                    > krewrite(Pattern, Pattern)       [non-assoc, klabel(krewrite)]
  syntax KLabel2 ::= LowerName
  syntax Symbol  ::= KLabel2
  syntax VarName ::= UpperName
endmodule

module EKORE0-DECLARATIONS-SYNTAX
  imports TOKENS
  imports EKORE1-DECLARATIONS-SYNTAX
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
```

K Frontend modules
==================

Since K and Kore have Modules and Definitions that differ slightly, we must
define a separate K (frontend) module syntax. Note that this module allows both
K and Kore declarations.

```k
module K-DEFINITION
  imports EKORE1-DECLARATIONS

  syntax KDefinition   ::= kDefinition(KRequireList, Modules) [klabel(kDefinition), format(%1%n%n%2)]
  syntax Definition    ::= KDefinition

  syntax KRequire      ::= kRequire(KString) [klabel(kRequire)]
  syntax KRequireList  ::= List{KRequire, ""}  [klabel(KRequireList), format(%1%2%n%3)]

  syntax KModule       ::= kModule( KModuleName
                                  , OptionalAttributes
                                  , KImportList
                                  , Declarations
                                  ) [klabel(kModule), format(%1 %2 %3%i%n%4%n%5%n%d%6)]
  syntax Module        ::= KModule
endmodule

module K-DEFINITION-SYNTAX
  imports EKORE1-DECLARATIONS-SYNTAX

  syntax KDefinition   ::= KRequireList Modules [klabel(kDefinition), format(%1%n%n%2)]
  syntax Definition    ::= KDefinition

  syntax KRequire      ::= "require" KString [klabel(kRequire)]
  syntax KRequireList  ::= List{KRequire, ""}  [klabel(KRequireList), format(%1%2%n%3)]

  syntax KModule       ::= "module" KModuleName OptionalAttributes
                                    KImportList
                                    Declarations
                           "endmodule"
                               [klabel(kModule), format(%1 %2 %3%i%n%4%n%5%n%d%6)]
  syntax Module        ::= KModule
endmodule
```

"main" modules
==============

For convenience, we also export combined modules:


```k
module EKORE-SYNTAX
  imports K-DEFINITION-SYNTAX
  imports TOKENS-SYNTAX
  imports EKORE0-DECLARATIONS-SYNTAX
endmodule

module EKORE
  imports K-DEFINITION
  imports EKORE0-DECLARATIONS
endmodule
```
