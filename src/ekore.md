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

EKORE extents the KORE syntax to allow:

1. `syntax` declarations,
2. `configuration`, `rule`s and `context`s, with contents as patterns
3. Patterns also allow `requires` and `=>`
4. Patterns also allow "backtick" syntax and `#token`

```k
module EKORE-SYNTAX
  imports KORE-SYNTAX
  imports K-PRODUCTION-SYNTAX
  imports CONFIG-RULE-CONTEXT-SYNTAX
  imports REWRITES-REQUIRES-IN-PATTERNS-SYNTAX
  imports BACKTICK-PATTERNS-SYNTAX
  imports K-DEFINITION-SYNTAX

  syntax Layout ::= r"(/\\*([^\\*]|(\\*+([^\\*/])))*\\*+/|//[^\n\r]*|[\\ \n\r\t])*" [klabel(layout)]
endmodule

module EKORE-ABSTRACT
  imports KORE-ABSTRACT
  imports K-PRODUCTION-ABSTRACT
  imports CONFIG-RULE-CONTEXT-ABSTRACT
  imports REWRITES-REQUIRES-IN-PATTERNS-ABSTRACT
  imports BACKTICK-PATTERNS-ABSTRACT
  imports K-DEFINITION-ABSTRACT
endmodule
```

Frontend
--------

```k
module OUTER-SYNTAX
  imports KORE-SYNTAX
  imports K-PRODUCTION-SYNTAX
  imports K-DEFINITION-SYNTAX
  imports RULES-WITH-BUBBLES-SYNTAX
  syntax Layout ::= r"(/\\*([^\\*]|(\\*+([^\\*/])))*\\*+/|//[^\n\r]*|[\\ \n\r\t])*" [klabel(layout)]
endmodule

module OUTER-ABSTRACT
  imports KORE-ABSTRACT
  imports K-PRODUCTION-ABSTRACT
  imports K-DEFINITION-ABSTRACT
  imports RULES-WITH-BUBBLES-ABSTRACT
endmodule

module RULES-WITH-BUBBLES-COMMON
  imports CONFIG-RULE-CONTEXT-COMMON
  syntax BubbleItem
  syntax Bubble
  syntax RuleContents ::= Bubble
endmodule

module RULES-WITH-BUBBLES-ABSTRACT
  imports RULES-WITH-BUBBLES-COMMON
  imports CONFIG-RULE-CONTEXT-ABSTRACT
endmodule

module RULES-WITH-BUBBLES-SYNTAX
  imports RULES-WITH-BUBBLES-COMMON
  imports CONFIG-RULE-CONTEXT-SYNTAX
  syntax BubbleItem ::= r"[^ \t\n\r]+" [token, reject2("rule|syntax|endmodule|configuration|context")]
  syntax Bubble ::= Bubble BubbleItem  [token]
                  | BubbleItem         [token]
endmodule
```

Extensions
==========

K Productions
-------------

```k
module EKORE-BASE
  imports KORE-COMMON
  syntax EKoreDeclaration
  syntax Declaration ::= EKoreDeclaration
endmodule
```

TODO: `OptionalAttributes` should be macro for `[]`
TODO: Combine with KORE's `Attribute`

```k
module K-PRODUCTION-COMMON
  imports EKORE-BASE
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
  syntax KPrioritySeq ::= KPrioritySeq ">" KNeTagSet         [klabel(kPrioritySeq)]
                        | KNeTagSet
  syntax ProdBlock ::= ProdBlock "|" KProductionWAttr [klabel(prodBlock), format(%1%n%2 %3)]
                     | KProductionWAttr
  syntax PrioritySeqBlock ::= PrioritySeqBlock ">" AssocAttribute ProdBlock [klabel(prioritySeqBlock), format(  %1%n%2 %3%4)]
                            | ProdBlock

  syntax KProductionItem
  syntax KProduction ::= KProductionItem
                       | KProductionItem KProduction [klabel(kProduction), unit(emptyKProduction)]
                       | Tag "(" KSortList ")"       [klabel(kFuncProduction)]
                       |     "(" KSortList ")"       [klabel(kTupleProduction)]

  syntax SyntaxDeclaration
    ::= "syntax" KSort OptionalAttributes [klabel(kSyntaxSort)]
      | "syntax" KSort "::=" PrioritySeqBlock [klabel(kSyntaxProduction), format(%1 %2 %3 %4)]
      | "syntax" "priority"   KPrioritySeq OptionalAttributes [klabel(kSyntaxPriority)]
      | "syntax" "priorities" KPrioritySeq OptionalAttributes [klabel(kSyntaxPriorities)]
      | "syntax" "left" KNeTagSet OptionalAttributes [klabel(kSyntaxLeft)]
      | "syntax" "right" KNeTagSet OptionalAttributes [klabel(kSyntaxRight)]
      | "syntax" "non-assoc" KNeTagSet OptionalAttributes [klabel(kSyntaxNonAssoc)]
  syntax EKoreDeclaration ::= SyntaxDeclaration
endmodule

module K-PRODUCTION-SYNTAX
  imports K-PRODUCTION-COMMON
  imports KORE-SYNTAX
  imports ATTRIBUTES-SYNTAX

  syntax AssocAttribute  ::= "" [klabel(noAttribute)]
  syntax KProductionItem ::= KSort       [klabel(nonTerminal)]
                           | EKoreKString     [klabel(terminal)]
                           | "r" EKoreKString [klabel(regexTerminal)]
                           | "NeList" "{" KSort "," EKoreKString "}" [klabel(neListProd)]
                           |   "List" "{" KSort "," EKoreKString "}" [klabel(listProd)]

endmodule

module K-PRODUCTION-ABSTRACT
  imports K-PRODUCTION-COMMON
  imports KORE-ABSTRACT

  syntax AssocAttribute  ::= "noAssoc" [klabel(noAttribute)]
  syntax KProductionItem ::= nonTerminal(KSort)              [klabel(nonTerminal), format(%3)]
                           | terminal(EKoreKString)          [klabel(terminal), format(%3)]
                           | regexTerminal(EKoreKString)     [klabel(regexTerminal)]
                           | neListProd(KSort, EKoreKString) [klabel(neListProd)]
                           | listProd(KSort,EKoreKString)    [klabel(listProd)]
endmodule
```

Configuration, Rules and Contexts
---------------------------------

```k
module CONFIG-RULE-CONTEXT-COMMON
  imports KORE-COMMON
  imports EKORE-BASE
  imports ATTRIBUTES-COMMON
  syntax RuleContents
  syntax EKoreDeclaration ::= "configuration" RuleContents [klabel(kConfiguration)]
                            | "rule"    RuleContents       [klabel(kRule)]
                            | "context" RuleContents       [klabel(kContext)]
endmodule

module CONFIG-RULE-CONTEXT-ABSTRACT
  imports CONFIG-RULE-CONTEXT-COMMON
  imports KORE-ABSTRACT
  syntax RuleContents ::= noAttrs(Pattern)                   [klabel(noAttrs), format(%3)]
                    | attrs(Pattern, KAttributesDeclaration) [klabel(attrs), prefer]
endmodule

module CONFIG-RULE-CONTEXT-SYNTAX
  imports CONFIG-RULE-CONTEXT-COMMON
  imports EKORE-KSTRING-SYNTAX
  imports KORE-SYNTAX
  syntax RuleContents ::= Pattern                        [klabel(noAttrs)]
                        | Pattern KAttributesDeclaration [klabel(attrs), prefer]
endmodule
```

EKoreKString
-------

We name this module differently to avoid conflicts the `domains.k`s version.

```k
module EKORE-KSTRING-COMMON
  syntax EKoreKString
endmodule

module EKORE-KSTRING-ABSTRACT
  imports EKORE-KSTRING-COMMON
endmodule

module EKORE-KSTRING-SYNTAX
  imports EKORE-KSTRING-COMMON
  // optionally qualified strings, like in Scala "abc", i"abc", r"a*bc", etc.
  syntax EKoreKString ::= r"[\\\"](([^\\\"\n\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]"      [token]
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

  syntax TagContent ::= UpperName | LowerName | Numbers | EKoreKString
  syntax TagContents
  syntax KEY ::= LowerName //[token] // TODO: this token attribute causes a lot of weird ambiguities

endmodule

module ATTRIBUTES-ABSTRACT
  imports ATTRIBUTES-COMMON
  syntax Attr ::= tagSimple(KEY)           [klabel(tagSimple), format(%3)]
                | KEY "(" TagContents ")"  [klabel(tagContent)]
  syntax AttrList ::= Attr "," AttrList    [klabel(consAttrList), format(%1 %2 %3)]
                    | ".AttrList"          [klabel(dotAttrList)]

  syntax OptionalAttributes ::= "noAtt" [klabel(noKAttributesDeclaration)]

  syntax TagContents ::= ".tagContents"  [klabel(dotTagContents), format()]
                       | TagContent TagContents [klabel(tagContents)]
endmodule

module ATTRIBUTES-SYNTAX
  imports ATTRIBUTES-COMMON
  imports TOKENS-SYNTAX

  syntax Attr ::= KEY                     [klabel(tagSimple)]
                | KEY "(" TagContents ")" [klabel(tagContent)]
  syntax EmptyAttrList ::= ""             [klabel(dotAttrList )]
  syntax NeAttrList    ::=  Attr "," NeAttrList [klabel(consAttrList)]
                         | Attr EmptyAttrList  [klabel(consAttrList)]
  syntax AttrList ::= NeAttrList | EmptyAttrList

  syntax OptionalAttributes ::= "" [klabel(noKAttributesDeclaration)]

  syntax TagContents ::= ""  [token, klabel(dotTagContents)]
                       | TagContent TagContents [token, klabel(tagContents)]
endmodule
```

Extend patterns with KAST syntax
--------------------------------

TODO: The current syntax is too generic allowing parsing ekore patterns of the form
KLabel(Arg1,..Arg2,..). The patterns allowed should be either proper kore, or
kast in "backtick" notation. The "Symbol" production in the following module has
to be changed accordingly.

```k
module REWRITES-REQUIRES-IN-PATTERNS-ABSTRACT
  imports KORE-ABSTRACT
  syntax Pattern ::= requiresClause(Pattern, Pattern) [klabel(requiresClause)]
                   > krewrite(Pattern, Pattern)       [non-assoc, klabel(krewrite), format(%3 => %5)]
endmodule

module REWRITES-REQUIRES-IN-PATTERNS-SYNTAX
  imports KORE-SYNTAX
  syntax Pattern ::=  Pattern "requires" Pattern [klabel(requiresClause)]
                    > Pattern "=>" Pattern [non-assoc, klabel(krewrite)]
endmodule

module BACKTICK-PATTERNS-ABSTRACT
  imports KORE-ABSTRACT
  imports EKORE-KSTRING-ABSTRACT
  syntax Variable ::= cast(VarName, KSort)             [klabel(cast)]
                    | VarName
  syntax Pattern  ::= ktoken(EKoreKString, EKoreKString)         [klabel(ktoken)]
                    | wrappedklabel(KLabel2)           [klabel(wrappedklabel)]
                    > ksequence(Pattern, Pattern)      [left, klabel(ksequence)]
  syntax KLabel2 ::= LowerName
  syntax Symbol  ::= KLabel2
  syntax VarName ::= UpperName
endmodule

module BACKTICK-PATTERNS-SYNTAX
  imports KORE-SYNTAX
  imports EKORE-KSTRING-SYNTAX
  syntax Variable ::= VarName
  syntax Pattern  ::= "#token" "(" EKoreKString "," EKoreKString ")" [klabel(ktoken)]
                    | "#klabel" "(" KLabel2 ")" [klabel(wrappedklabel)]
                    | Pattern "requires" Pattern [klabel(requiresClause)]
                    > Pattern "~>" Pattern [left, klabel(ksequence)]
  syntax KLabel2 ::= LowerName | BacktickName

  syntax Symbol  ::= KLabel2
  syntax VarName ::= UpperName | DollarName
endmodule
```

K Frontend modules
------------------

Since K and Kore have Modules and Definitions that differ slightly, we must
define a separate K (frontend) module syntax. Note that this module allows both
K and Kore declarations.

TODO: Make these macros for the corresponding kore concepts

```k
module K-DEFINITION-COMMON
  imports TOKENS
  imports EKORE-KSTRING-COMMON

  syntax KImport       ::= "imports" KModuleName [klabel(kImport)]
  syntax KImportList

  syntax KRequire      ::= kRequire(EKoreKString) [klabel(kRequire)]
  syntax KRequireList
endmodule

module K-DEFINITION-ABSTRACT
  imports K-DEFINITION-COMMON
  imports KORE-ABSTRACT
  imports ATTRIBUTES-ABSTRACT

  syntax KImportList   ::= ".KImportList" [klabel(emptyKImportList)]
                         | KImportList KImport  [klabel(kImportList), format(%1%2%n)]
  syntax KRequireList  ::= ".KRequireList" [klabel(emptyKRequireList)]
                         | KRequireList KRequire [klabel(KRequireList), format(%1%2%n)]

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

