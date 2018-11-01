```k
requires "ekore.k"
```

```k
module KINK-CONFIGURATION
  imports EKORE-ABSTRACT

  syntax K ::= "#initPipeline"
  configuration <pipeline> #initPipeline  </pipeline>
                <k> $PGM:Definition </k>
endmodule
```

Visitor Infrastructure
----------------------

This section defines visitors which are used in tranformations.

```k
module KINK-VISITORS
  imports KINK-CONFIGURATION
  imports KORE-HELPERS
```

A Visitor Action consists of an "action" to be performed on
every sentence. To use the visitors, extend the Action sort.

```k
  syntax Action

  syntax Visitor ::= #visitDefintion(Action)
                   | #visitModules(Action, Modules)
                   | #visitModulesAux(Modules)
                   | #visitSentences(Action, Declarations)

  syntax Visitor ::= #visitModule(Action, Module)

  rule <pipeline> #visitDefintion(VA) => #visitModules(VA, MODULES) ... </pipeline>
       <k> koreDefinition(ATTR, MODULES) => koreDefinition(ATTR, .Modules) </k>

  rule <pipeline> #visitModules(VA, M MS) => #visitModule(VA, M) ~> #visitModulesAux(MS) ... </pipeline>
  rule <pipeline> VA ~> #visitModulesAux(MS) => #visitModules(VA, MS) ... </pipeline>
  rule <pipeline> #visitModules(VA, .Modules) => VA ... </pipeline>

  syntax KItem ::= #sentencesIntoModule(KoreName, Attribute)

  rule <pipeline> #visitModule(VA, koreModule(MNAME, DECLS, ATTRS))
              =>  #visitSentences(VA, DECLS) ~> #sentencesIntoModule(MNAME, ATTRS) ... </pipeline>


  syntax KItem ::= #applyActionToSentence(Action, Declaration)
                 | #visitSentencesAux(Declarations)

  rule <pipeline> #visitSentences(VA, DECL DECLS)
               => #applyActionToSentence(VA, DECL) ~> #visitSentencesAux(DECLS) ... </pipeline>

```
The following construct a transformed module and place
it back into the `<k>` cell. A `#applicationResult`
is the result of applying an `Action` on a `Sentence`.

```k
  syntax KItem ::= #applicationResult(Declarations, Action)
                 | #processedSentences(Declarations, Action)

  rule <pipeline> #applicationResult(PROCESSED_DECLS, VA) ~> #visitSentencesAux(DECLS)
               => #visitSentences(VA, DECLS) ~> #processedSentences(PROCESSED_DECLS, VA) ... </pipeline>

  rule <pipeline> #applicationResult(PROCESSED_DECLS, VA) ~> #visitSentencesAux(.Declarations)
               => #processedSentences(PROCESSED_DECLS, VA) ... </pipeline>

  rule <pipeline> #processedSentences(DECLS1, VA2) ~> #processedSentences(DECLS2, VA1)
               => #processedSentences(DECLS2 ++Declarations DECLS1, VA2) ... </pipeline>

  rule <pipeline> #processedSentences(DECLS, VA) ~> #sentencesIntoModule(MNAME,MATTR)
               => VA  ... </pipeline>
        <k> koreDefinition(ATTR, MS)
         => koreDefinition(ATTR,  MS ++Modules koreModule(MNAME, DECLS, MATTR) .Modules) </k>

endmodule
```

Transformations
===============

K (frontend) modules to Kore Modules
------------------------------------

Since the visitor infrastructure only works over Kore modules and definitions,
frontend modules must be converted to kore modules first.

TODO: This needs to convert the modules into a topological order and check for cycles.

```k
module K-MODULE-TO-KORE-MODULE
  imports KINK-CONFIGURATION

  rule kDefinition(_:KRequireList, MODS:Modules)
    => koreDefinition([ .Patterns ], MODS:Modules)
  rule kModule(MNAME:KModuleName, ATTRS:OptionalAttributes, KIMPORTS:KImportList, DECLS:Declarations)
    => koreModule(MNAME:KModuleName, DECLS:Declarations, [ .Patterns ])
       [anywhere]
endmodule
```


Extract sorts from productions
------------------------------

This transformation adds `sort` declarations for each production.

```k
module EXTRACT-SORTS-FROM-PRODUCTIONS
  imports KINK-VISITORS
  imports SET

  syntax KItem ::= "#extractKoreSortsFromProductions"
```
We first collect all sorts that have already been declared in the definition.

```k
  syntax Action ::= #collectDeclaredSorts(Set)

  rule <pipeline> #applyActionToSentence( #collectDeclaredSorts(DECLARED_SORTS)
                                        , sort KORE_NAME { KORE_NAMES } ATTRS
                                        )
              =>  #applicationResult( sort KORE_NAME { KORE_NAMES } ATTRS .Declarations
                                    , #collectDeclaredSorts(DECLARED_SORTS SetItem(KORE_NAME))
                                    ) ...
       </pipeline> [prefer]

  rule <pipeline> #applyActionToSentence( #collectDeclaredSorts(DECLARED_SORTS)
                                        , DECL
                                        )
              =>  #applicationResult( DECL .Declarations
                                    , #collectDeclaredSorts(DECLARED_SORTS)
                                    ) ...
       </pipeline>
```

`sortNameFromProdDecl` extracts the name of the sort from the `KProductionDeclaration`

```k
  syntax KoreName ::= sortNameFromProdDecl(KProductionDeclaration) [function]
  rule sortNameFromProdDecl(kSyntaxProduction(KSORT:UpperName, _)) => KSORT
```

We use our visitor infrastructure here to implement the
`#extractKoreSortsFromProductions` pipeline step.
We extend the `Action` sort, and use the `#applicationResult` construct
to indicate the result of applying the action.
Notice that we return a modified `Action` as the second argument of
our result. The modified action allows threading state through
the visitors.

```k
  syntax Action ::= #extractSortsFromProductions(Set)

  rule <pipeline> #extractKoreSortsFromProductions
               => #visitDefintion(#collectDeclaredSorts(.Set))
                  ~> #visitDefintion(#extractSortsFromProductions(.Set)) ... </pipeline>

  rule <pipeline> #collectDeclaredSorts(DECLARED_SORTS)
                  ~> #visitDefintion(#extractSortsFromProductions(_))
               => #visitDefintion(#extractSortsFromProductions(DECLARED_SORTS)) ... </pipeline>
```
Once we're done with our visitors, we clean up the `<k>` cell, by removing our
state containing action.

```k
  rule <pipeline> #extractSortsFromProductions(_) => .K  </pipeline>
```

```k

  rule <pipeline>
           #applyActionToSentence( #extractSortsFromProductions(DECLARED_SORTS)
                                 , DECL:KProductionDeclaration
                                 )
        => #applicationResult( sort sortNameFromProdDecl(DECL) { .KoreNames } [ .Patterns ] DECL .Declarations
                             , #extractSortsFromProductions(DECLARED_SORTS SetItem(sortNameFromProdDecl(DECL)))
                             ) ...
       </pipeline>
       requires notBool(sortNameFromProdDecl(DECL) in DECLARED_SORTS)
```

A sort declaration already exists, ignore:

```k
  rule <pipeline>
           #applyActionToSentence( #extractSortsFromProductions(DECLARED_SORTS)
                                 , DECL:KProductionDeclaration
                                 )
        => #applicationResult( DECL .Declarations
                             , #extractSortsFromProductions(DECLARED_SORTS SetItem(sortNameFromProdDecl(DECL)))
                             ) ...
       </pipeline>
       requires sortNameFromProdDecl(DECL) in DECLARED_SORTS

  rule <pipeline>
           #applyActionToSentence( #extractSortsFromProductions(DECLARED_SORTS)
                                 , sort KORE_NAME:KoreName { KORE_NAMES } ATTRS
                                 )
        => #applicationResult(  sort KORE_NAME:KoreName { KORE_NAMES } ATTRS .Declarations
                             , #extractSortsFromProductions(DECLARED_SORTS SetItem(KORE_NAME))
                             ) ...
       </pipeline> [prefer]
```

Ignore other `Declaration`s:

```k
   // TODO: This is a hack
   rule isKProductionDeclaration(sort KORE_NAME:KoreName { KORE_NAMES } ATTRS)
     => true
   rule <pipeline>
            #applyActionToSentence( #extractSortsFromProductions(DECLARED_SORTS)
                                  , DECL
                                  )
         => #applicationResult( DECL .Declarations
                              , #extractSortsFromProductions(DECLARED_SORTS)
                              ) ...
        </pipeline>
     requires notBool(isKProductionDeclaration(DECL))
endmodule
```

```k
module KINK
  imports K-MODULE-TO-KORE-MODULE
  imports EXTRACT-SORTS-FROM-PRODUCTIONS

  rule <pipeline> #initPipeline
               => #extractKoreSortsFromProductions
                  ...
       </pipeline>
endmodule
```

