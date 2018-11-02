```k
requires "ekore.k"
```

```k
module KINK-CONFIGURATION
  imports EKORE-ABSTRACT
  imports SET

  syntax K ::= "#initPipeline"
```

The `<koreModule>` cell has to be named as such, instead
of the more natural `<module>` as K isn't able to parse the
cell name as such, instead parsing the token as the `module` keyword.
```k
  configuration <pipeline> #initPipeline  </pipeline>
                <k> $PGM:Definition </k>
                <koreModules>
                  <koreModule multiplicity="*" type="Map">
                    <name> .K </name>
                    <sorts> .Set </sorts>
                  </koreModule>
                </koreModules>
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
  syntax Visitor

  syntax VisitorHelper ::= #visitDefintion(Visitor)
                         | #visitModules(Visitor, Modules)
                         | #visitModulesAux(Modules)
                         | #visitSentences(Visitor, Declarations)

  syntax VisitorHelper ::= #visitModule(Visitor, Module)

  rule <pipeline> #visitDefintion(VA) => #visitModules(VA, MODULES) ... </pipeline>
       <k> koreDefinition(ATTR, MODULES) => koreDefinition(ATTR, .Modules) </k>

  rule <pipeline> #visitModules(VA, M MS) => #visitModule(VA, M) ~> #visitModulesAux(MS) ... </pipeline>
  rule <pipeline> VA ~> #visitModulesAux(MS) => #visitModules(VA, MS) ... </pipeline>
  rule <pipeline> #visitModules(VA, .Modules) => VA ... </pipeline>

  syntax VisitorHelper ::= #sentencesIntoModule(KoreName, Attribute)

  rule <pipeline> #visitModule(VA, koreModule(MNAME, DECLS, ATTRS))
              =>  #visitSentences(VA, DECLS) ~> #sentencesIntoModule(MNAME, ATTRS)
                  ...
       </pipeline>


  syntax VisitorHelper ::= #visit(Visitor, Declaration)
                         | #visitSentencesAux(Declarations)

  rule <pipeline> #visitSentences(VA, DECL DECLS)
               => #visit(VA, DECL) ~> #visitSentencesAux(DECLS)
                  ...
       </pipeline>

  rule <pipeline> #visitSentences(VA, .Declarations)
               => .K ... </pipeline>

```
The following construct a transformed module and place
it back into the `<k>` cell. A `#visitResult`
is the result of applying an `Action` on a `Sentence`.

```k
  syntax KItem ::= #visitResult(Declarations, Visitor)
                 | #processedSentences(Declarations, Visitor)

  rule <pipeline> #visitResult(PROCESSED_DECLS, VA) ~> #visitSentencesAux(DECLS)
               => #visitSentences(VA, DECLS) ~> #processedSentences(PROCESSED_DECLS, VA)
                  ...
       </pipeline>

  rule <pipeline> #visitResult(PROCESSED_DECLS, VA) ~> #visitSentencesAux(.Declarations)
               => #processedSentences(PROCESSED_DECLS, VA)
                  ...
       </pipeline>

  rule <pipeline> #processedSentences(DECLS1, VA2) ~> #processedSentences(DECLS2, VA1)
               => #processedSentences(DECLS2 ++Declarations DECLS1, VA2)
                   ...
       </pipeline>

  rule <pipeline> #processedSentences(DECLS, VA) ~> #sentencesIntoModule(MNAME,MATTR)
               => VA
                  ...
        </pipeline>
        <k> koreDefinition(ATTR, MS)
         => koreDefinition(ATTR,  MS ++Modules koreModule(MNAME, DECLS, MATTR) .Modules)
        </k>

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
  imports KORE-HELPERS

  syntax K ::= "#frontendModulesToKoreModules"
             | #toKoreModules(Modules)

  rule <pipeline> #frontendModulesToKoreModules => .K
                  ...
       </pipeline>
       <k> kDefinition(_:KRequireList, MODS)
        => #toKoreModules(MODS) ~> koreDefinition([ .Patterns ], .Modules)
       </k>

  rule #toKoreModules(M MS)     => M ~> #toKoreModules(MS)
  rule #toKoreModules(.Modules) => .K

  rule <k> kModule(MNAME, ATTRS, KIMPORTS, DECLS)
           ~> #toKoreModules(MODULES)
           ~> koreDefinition([ .Patterns ], PROCESSED_MODULES:Modules)
        => #toKoreModules(MODULES)
           ~> koreDefinition( [ .Patterns ]
                            ,  PROCESSED_MODULES ++Modules (koreModule(MNAME, DECLS, [ .Patterns]) .Modules)
                            )
           ...
       </k>
       <koreModules> ( .Bag
                => <koreModule>
                    <name> MNAME </name>
                    <sorts> .Set </sorts>
                   </koreModule>
                 )
        ...
       </Modules>
```
TODO: Generalize this to remove following rule

If ekore defintion is already a kore definition,
then ignore the conversion, but populate the configuration.

```k
  rule <pipeline> #frontendModulesToKoreModules => .K
                  ...
       </pipeline>
       <k> koreDefinition(ATTRS, MODS)
        => #toKoreModules(MODS) ~> koreDefinition(ATTRS, .Modules)
       </k>

  rule <k> koreModule(MNAME, DECLS:Declarations, ATTRS)
           ~> #toKoreModules(MODULES)
           ~> koreDefinition([ .Patterns ], PROCESSED_MODULES:Modules)
        => #toKoreModules(MODULES)
           ~> koreDefinition( [ .Patterns ]
                            ,  PROCESSED_MODULES ++Modules (koreModule(MNAME, DECLS, ATTRS) .Modules)
                            )
           ...
       </k>
       <Modules> ( .Bag
                => <Module>
                    <name> MNAME </name>
                    <sorts> .Set </sorts>
                   </Module>
                 )
        ...
       </Modules>
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
  syntax Visitor ::= #collectDeclaredSorts(Set)

  rule <pipeline> #visit( #collectDeclaredSorts(DECLARED_SORTS)
                        , sort KORE_NAME { KORE_NAMES } ATTRS
                        )
              =>  #visitResult( sort KORE_NAME { KORE_NAMES } ATTRS .Declarations
                              , #collectDeclaredSorts(DECLARED_SORTS SetItem(KORE_NAME))
                              )
                  ...
       </pipeline>

  rule <pipeline> #visit( #collectDeclaredSorts(DECLARED_SORTS)
                        , DECL
                        )
              =>  #visitResult( DECL .Declarations
                              , #collectDeclaredSorts(DECLARED_SORTS)
                              )
                  ...
       </pipeline>
       requires notBool isSortDeclaration(DECL)
```

`sortNameFromProdDecl` extracts the name of the sort from the `KProductionDeclaration`

```k
  syntax KoreName ::= sortNameFromProdDecl(KProductionDeclaration) [function]
  rule sortNameFromProdDecl(kSyntaxProduction(KSORT:UpperName, _)) => KSORT
```

We use our visitor infrastructure here to implement the
`#extractKoreSortsFromProductions` pipeline step.
We extend the `Action` sort, and use the `#visitResult` construct
to indicate the result of applying the action.
Notice that we return a modified `Action` as the second argument of
our result. The modified action allows threading state through
the visitors.

```k
  syntax Visitor ::= #extractSortsFromProductions(Set)

  rule <pipeline> #extractKoreSortsFromProductions
               => #visitDefintion(#collectDeclaredSorts(.Set))
                  ~> #visitDefintion(#extractSortsFromProductions(.Set))
                  ...
       </pipeline>

  rule <pipeline> #collectDeclaredSorts(DECLARED_SORTS)
                  ~> #visitDefintion(#extractSortsFromProductions(_))
               => #visitDefintion(#extractSortsFromProductions(DECLARED_SORTS))
               ...
      </pipeline>
```
Once we're done with our visitors, we clean up the `<k>` cell, by removing our
state containing action.

```k
  rule <pipeline> #extractSortsFromProductions(_) => .K  </pipeline>
```

```k

  rule <pipeline>
           #visit( #extractSortsFromProductions(DECLARED_SORTS)
                 , DECL:KProductionDeclaration
                 )
        => #visitResult( sort sortNameFromProdDecl(DECL) { .KoreNames } [ .Patterns ] DECL .Declarations
                       , #extractSortsFromProductions(DECLARED_SORTS SetItem(sortNameFromProdDecl(DECL)))
                       )
           ...
       </pipeline>
       requires notBool(sortNameFromProdDecl(DECL) in DECLARED_SORTS)
```

A sort declaration already exists, ignore:

```k
  rule <pipeline>
           #visit( #extractSortsFromProductions(DECLARED_SORTS)
                 , DECL:KProductionDeclaration
                 )
        => #visitResult( DECL .Declarations
                       , #extractSortsFromProductions(DECLARED_SORTS SetItem(sortNameFromProdDecl(DECL)))
                       )
           ...
       </pipeline>
       requires sortNameFromProdDecl(DECL) in DECLARED_SORTS

  rule <pipeline>
           #visit( #extractSortsFromProductions(DECLARED_SORTS)
                 , sort KORE_NAME:KoreName { KORE_NAMES } ATTRS
                 )
        => #visitResult( sort KORE_NAME:KoreName { KORE_NAMES } ATTRS .Declarations
                       , #extractSortsFromProductions(DECLARED_SORTS SetItem(KORE_NAME))
                       )
           ...
       </pipeline>
```

Ignore other `Declaration`s:

```k
   rule <pipeline>
            #visit( #extractSortsFromProductions(DECLARED_SORTS)
                  , DECL
                  )
         => #visitResult( DECL .Declarations
                        , #extractSortsFromProductions(DECLARED_SORTS)
                        )
            ...
        </pipeline>
     requires notBool(isKProductionDeclaration(DECL))
endmodule
```

```k
module KINK
  imports K-MODULE-TO-KORE-MODULE
  imports EXTRACT-SORTS-FROM-PRODUCTIONS

  rule <pipeline> #initPipeline
               => #frontendModulesToKoreModules
                  ~> #visitDefintion(#collectDeclaredSorts)
                  ~> #visitDefintion(#extractSortsFromProductions)
                  ...
       </pipeline>
endmodule
```

