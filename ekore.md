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
writing rules over (suffixed with `-ABSTRACT`). We may also define a third
module (suffixed `-COMMON`) with code that these two modules can share.

EKORE
-----

In addition to the `EKORE0` syntax, `EKORE` also allows K Frontend modules and
definitions.

```k
module EKORE-SYNTAX
  imports K-DEFINITION-SYNTAX
  imports EKORE0-SYNTAX

  syntax Layout ::= r"(/\\*([^\\*]|(\\*+([^\\*/])))*\\*+/|//[^\n\r]*|[\\ \n\r\t])*" [klabel(layout)]
endmodule

module EKORE-ABSTRACT
  imports K-DEFINITION-ABSTRACT
  imports EKORE0-ABSTRACT
endmodule
```

EKore 0
-------

`EKORE0` extends `EKORE1` allowing the use of "backtick" kast syntax, `#token`,
rewrite and sequencing arrows.

```k
module EKORE0-SYNTAX
  imports EKORE1-SYNTAX
  imports EXTEND-PATTERNS-WITH-KAST-SYNTAX
endmodule

module EKORE0-ABSTRACT
  imports EKORE1-ABSTRACT
  imports EXTEND-PATTERNS-WITH-KAST-ABSTRACT
endmodule
```

EKore 1
-------

EKORE1 extends KORE with frontend syntax for `syntax`, `rule`s,
`configuration` and `context`s. Rules do not allow for concrete language syntax
or even kast syntax, but only for the Kore notation for referencing symbols.

```k
module EKORE1-COMMON
  syntax KFrontendDeclaration
  syntax Declaration ::= KFrontendDeclaration
endmodule

module EKORE1-ABSTRACT
  imports EKORE1-COMMON
  imports K-PRODUCTION-ABSTRACT
  imports CONFIG-RULE-CONTEXT-ABSTRACT
endmodule

module EKORE1-SYNTAX
  imports EKORE1-COMMON
  imports K-PRODUCTION-SYNTAX
  imports CONFIG-RULE-CONTEXT-SYNTAX
endmodule
```

Extensions
==========

K Productions
-------------

```k
module K-PRODUCTION-COMMON
  imports KORE-COMMON
  imports ATTRIBUTES-COMMON

  syntax Tag ::= UpperName | LowerName
  syntax KNeTagSet    ::= Tag KNeTagSet [klabel(kTagSet)]
                        | Tag

  syntax AssocAttribute ::= "left:"      [klabel(leftAttribute)]
                          | "right:"     [klabel(rightAttribute)]
                          | "non-assoc:" [klabel(nonAssocAttribute)]

  syntax KSortList ::= KSortList "," KSort [klabel(kSortList)]
                     | KSort
  syntax KProductionWAttr ::= KProduction OptionalAttributes [klabel(kProductionWAttr)]
                            | Tag "(" KSortList ")" OptionalAttributes [klabel(kFuncProductionWAttr)]
                            |     "(" KSortList ")" OptionalAttributes [klabel(kTupleProductionWAttr)]
  syntax KPrioritySeq ::= KPrioritySeq ">" KNeTagSet   [klabel(kPrioritySeq)]
                        | KNeTagSet
  syntax ProdBlock ::= ProdBlock "|" KProductionWAttr [klabel(prodBlock), format(%1%n%2 %3)]
                     | KProductionWAttr
  syntax PrioritySeqBlock ::= PrioritySeqBlock ">" AssocAttribute ProdBlock [klabel(prioritySeqBlock), format(  %1%n%2 %3%4)]
                            | ProdBlock

  syntax KProductionItem
  syntax KProduction ::= KProductionItem
                       | KProduction KProductionItem [klabel(kProduction), unit(emptyKProduction)]

  syntax KProductionDeclaration
    ::= "syntax" KSort OptionalAttributes [klabel(kSyntaxSort)]
      | "syntax" KSort "::=" PrioritySeqBlock [klabel(kSyntaxProduction), format(%1 %2 %3%i%n%4%d)]
      | "syntax" "priority"   KPrioritySeq OptionalAttributes [klabel(kSyntaxPriority)]
      | "syntax" "priorities" KPrioritySeq OptionalAttributes [klabel(kSyntaxPriorities)]
      | "syntax" "left" KNeTagSet OptionalAttributes [klabel(kSyntaxLeft)]
      | "syntax" "right" KNeTagSet OptionalAttributes [klabel(kSyntaxRight)]
      | "syntax" "non-assoc" KNeTagSet OptionalAttributes [klabel(kSyntaxNonAssoc)]
  syntax KFrontendDeclaration ::= KProductionDeclaration
endmodule

module K-PRODUCTION-SYNTAX
  imports K-PRODUCTION-COMMON
  imports KORE-SYNTAX
  imports ATTRIBUTES-SYNTAX

  syntax AssocAttribute  ::= "" [klabel(noAttribute)]
  syntax KProductionItem ::= KSort       [klabel(nonTerminal)]
                           | KString     [klabel(terminal)]
                           | "r" KString [klabel(regexTerminal)]
                           | "NeList" "{" KSort "," KString "}" [klabel(neListProd)]
                           |   "List" "{" KSort "," KString "}" [klabel(listProd)]

endmodule

module K-PRODUCTION-ABSTRACT
  imports K-PRODUCTION-COMMON
  imports KORE-ABSTRACT

  syntax AssocAttribute  ::= "noAssoc" [klabel(noAttribute)]
  syntax KProductionItem ::= nonTerminal(KSort)         [klabel(nonTerminal)]
                           | terminal(KString)          [klabel(terminal), format(%3)]
                           | regexTerminal(KString)     [klabel(regexTerminal)]
                           | neListProd(KSort, KString) [klabel(neListProd)]
                           | listProd(KSort,KString)    [klabel(listProd)]
endmodule
````

Configuration, Rules and Contexts
---------------------------------

```k
module CONFIG-RULE-CONTEXT-COMMON
  imports KORE-COMMON
  imports ATTRIBUTES-COMMON
  syntax Contents
  syntax KFrontendDeclaration ::= "configuration" Contents [klabel(kConfiguration)]
                                | "rule"    Contents [klabel(kRule)]
                                | "context" Contents [klabel(kContext)]
endmodule

module CONFIG-RULE-CONTEXT-ABSTRACT
  imports CONFIG-RULE-CONTEXT-COMMON
  imports KORE-ABSTRACT
  syntax Contents ::= noAttrs(Pattern)                       [klabel(noAttrs), format(%3)]
                    | attrs(Pattern, KAttributesDeclaration) [klabel(attrs), prefer]
endmodule

module CONFIG-RULE-CONTEXT-SYNTAX
  imports CONFIG-RULE-CONTEXT-COMMON
  imports KORE-SYNTAX
  syntax Contents ::= Pattern                        [klabel(noAttrs)]
                    | Pattern KAttributesDeclaration [klabel(attrs), prefer]
endmodule
```

KString
-------

We name this module differently to avoid conflicts the `domains.k`s version.

```k
module EKORE-KSTRING-SYNTAX
  imports EKORE-KSTRING-COMMON
  // optionally qualified strings, like in Scala "abc", i"abc", r"a*bc", etc.
  syntax KString ::= r"[\\\"](([^\\\"\n\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]"      [token]
endmodule

module EKORE-KSTRING-COMMON
  syntax KString
endmodule
```

Attributes
----------

Attributes are use both by KModules/Definitions and Productions

```k
module ATTRIBUTES-COMMON
  imports EKORE-KSTRING-COMMON
  imports TOKENS

  syntax Attr
  syntax AttrList
  syntax KAttributesDeclaration ::= "[" AttrList "]" [klabel(kAttributesDeclaration)]
  syntax OptionalAttributes ::= KAttributesDeclaration

  syntax TagContent ::= UpperName | LowerName | Numbers
  syntax TagContents
  syntax KEY ::= LowerName
endmodule

module ATTRIBUTES-ABSTRACT
  imports ATTRIBUTES-COMMON
  syntax Attr ::= tagSimple(LowerName)    [klabel(tagSimple), format(%3)]
                | KEY "(" TagContents ")" [klabel(tagContent)]
                | KEY "(" KString ")"     [klabel(tagString)]
  syntax OptionalAttributes ::= "noAtt" [klabel(noKAttributesDeclaration)]
endmodule

module ATTRIBUTES-SYNTAX
  imports ATTRIBUTES-COMMON
  imports TOKENS-SYNTAX
  syntax Attr ::= KEY                     [klabel(tagSimple)]
                | KEY "(" TagContents ")" [klabel(tagContent)]
                | KEY "(" KString ")"     [klabel(tagString)]
  syntax EmptyAttrList ::= ""             [klabel(dotAttrList )]
  syntax NeAttrList    ::=  Attr "," NeAttrList [klabel(consAttrList)]
                         | Attr EmptyAttrList  [klabel(consAttrList)]
  syntax AttrList ::= NeAttrList | EmptyAttrList

  syntax OptionalAttributes ::= "" [klabel(noKAttributesDeclaration)]
endmodule
```

Extend patterns with KAST syntax
--------------------------------

TODO: The current syntax is too generic allowing parsing ekore patterns of the form
KLabel(Arg1,..Arg2,..). The patterns allowed should be either proper kore, or
kast in "backtick" notation. The "Symbol" production in the following module has
to be changed accordingly.

```k
module EXTEND-PATTERNS-WITH-KAST-ABSTRACT
  imports TOKENS
  imports EKORE1-ABSTRACT
  syntax Variable ::= cast(VarName, KSort) [klabel(cast)]
                    | VarName
  syntax Pattern  ::= ktoken(KString, KString)         [klabel(ktoken)]
                    | wrappedklabel(KLabel2)           [klabel(wrappedklabel)]
                    | requiresClause(Pattern, Pattern) [klabel(requiresClause)]
                    > ksequence(Pattern, Pattern)      [left, klabel(ksequence)]
                    > krewrite(Pattern, Pattern)       [non-assoc, klabel(krewrite), format(%3 => %5)]
  syntax KLabel2 ::= LowerName
  syntax Symbol  ::= KLabel2
  syntax VarName ::= UpperName
endmodule

module EXTEND-PATTERNS-WITH-KAST-SYNTAX
  imports TOKENS
  imports EKORE1-SYNTAX
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
------------------

Since K and Kore have Modules and Definitions that differ slightly, we must
define a separate K (frontend) module syntax. Note that this module allows both
K and Kore declarations.

```k
module K-DEFINITION-COMMON
  imports TOKENS

  syntax KImport       ::= "imports" KModuleName [klabel(kImport)]
  syntax KImportList

  syntax KRequire      ::= kRequire(KString) [klabel(kRequire)]
  syntax KRequireList
endmodule

module K-DEFINITION-ABSTRACT
  imports K-DEFINITION-COMMON
  imports KORE-ABSTRACT
  imports ATTRIBUTES-ABSTRACT

  syntax KImportList   ::= ".KImportList" [klabel(emptyKImportList)]
                         | KImportList KImport  [klabel(kImportList), format(%1%2%n%3)]
  syntax KRequireList  ::= ".KRequireList" [klabel(emptyKRequireList)]
                         | KRequireList KRequire [klabel(KRequireList), format(%1%2%n%3)]

  syntax KDefinition   ::= kDefinition(KRequireList, Modules) [klabel(kDefinition), format(%3%n%n%5)]
  syntax Definition    ::= KDefinition

  syntax KModule       ::= kModule( KModuleName
                                  , OptionalAttributes
                                  , KImportList
                                  , Declarations
                                  ) [klabel(kModule)]
  syntax Module        ::= KModule
endmodule

module K-DEFINITION-SYNTAX
  imports K-DEFINITION-COMMON
  imports EKORE-KSTRING-SYNTAX
  imports KORE-SYNTAX
  imports ATTRIBUTES-SYNTAX

  syntax KImportList   ::= "" [klabel(emptyKImportList)]
                         | KImportList KImport  [klabel(kImportList), format(%1%2%n%3)]
  syntax KRequireList  ::= "" [klabel(emptyKRequireList)]
                         | KRequireList KRequire [klabel(KRequireList), format(%1%2%n%3)]

  syntax KDefinition   ::= KRequireList Modules [klabel(kDefinition), format(%1%n%n%2)]
  syntax Definition    ::= KDefinition

  syntax KModule       ::= "module" KModuleName OptionalAttributes
                                    KImportList
                                    Declarations
                           "endmodule"
                               [klabel(kModule), format(%1 %2 %3%i%n%4%n%5%n%d%6)]
  syntax Module        ::= KModule
endmodule
```

