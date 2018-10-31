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

```k
module KINK-VISITORS
  imports KINK-CONFIGURATION
  imports KORE-HELPERS

  syntax Visitor

  syntax K ::= #forEachSentence(Visitor)
  syntax K ::= #visitNext(Visitor, Declarations)    // Visitor, Declarations returned by Visitor
             | #visitModules(Modules, Declarations)
             | #visitSentence(Visitor, Declarations)

  rule <pipeline> #forEachSentence(V)
               => #visitNext(V, .Declarations) ~> #visitModules(MODULES, .Declarations)
       </pipeline>
       <k> koreDefinition(ATTR:Attribute, MODULES)
        => koreDefinition(ATTR:Attribute, .Modules)
       </k>

  rule <pipeline> #visitNext(V, DECLS_NEW) ~> #visitModules(MODULES, DECLS_OLD)
               => #visitNext(V, .Declarations) ~>
                  #visitModules(MODULES, DECLS_OLD ++Declarations DECLS_NEW)
       </pipeline>

  rule <pipeline> #visitNext(V, .Declarations) ~>
                  #visitModules(koreModule(MNAME, DECL:Declaration DECLS, ATTRS) MODULES, TRANSFORMED_DECLS)
               => #visitSentence(V, DECL) ~>
                  #visitModules(koreModule(MNAME, DECLS, ATTRS) MODULES, TRANSFORMED_DECLS)
       </pipeline>

  rule <pipeline> #visitNext(V, .Declarations) ~>
                  #visitModules(koreModule(MNAME, .Declarations, ATTRS:Attribute) REM_MODULES, TRANSFORMED_DECLS)
               => #visitSentence(V, .Declarations) ~>
                  #visitModules(REM_MODULES, .Declarations)
       </pipeline>
       <k> ATTRS (   TRANSFORMED_MODULES
                  => TRANSFORMED_MODULES ++Modules (koreModule(MNAME, TRANSFORMED_DECLS, ATTRS) .Modules)
                 )
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
```

`sortNameFromProdDecl` extracts the name of the sort from the `KProductionDeclaration`

```k
  syntax KoreName ::= sortNameFromProdDecl(KProductionDeclaration) [function]
  rule sortNameFromProdDecl(kSyntaxProduction(KSORT:UpperName, _)) => KSORT
```

Create a sort declaration:

```k
  syntax Visitor ::= #extractSortsFromProductions(Set)

  rule <pipeline> #visitSentence( #extractSortsFromProductions(DECLARED_SORTS)
                                , DECL:KProductionDeclaration
                                )
               => #visitNext( #extractSortsFromProductions(DECLARED_SORTS SetItem(sortNameFromProdDecl(DECL)))
                            , sort sortNameFromProdDecl(DECL) { .KoreNames } [ .Patterns ]
                              DECL
                              .Declarations
                            )
                  ...
       </pipeline>
    requires notBool(sortNameFromProdDecl(DECL) in DECLARED_SORTS)
```

A sort declaration already exists, ignore:

```k
  rule <pipeline> #visitSentence( #extractSortsFromProductions(DECLARED_SORTS)
                                , DECL:KProductionDeclaration
                                )
               => #visitNext( #extractSortsFromProductions(DECLARED_SORTS SetItem(sortNameFromProdDecl(DECL)))
                            , DECL
                              .Declarations
                            )
                  ...
       </pipeline>
    requires sortNameFromProdDecl(DECL) in DECLARED_SORTS

  rule <pipeline> #visitSentence( #extractSortsFromProductions(DECLARED_SORTS)
                                , sort KORE_NAME:KoreName { KORE_NAMES } ATTRS
                                )
               => #visitNext( #extractSortsFromProductions(DECLARED_SORTS SetItem(KORE_NAME))
                            , sort KORE_NAME:KoreName { KORE_NAMES } ATTRS
                              .Declarations
                            )
                  ...
       </pipeline>
```

Ignore other `Declaration`s:

```k
  // TODO: This is a hack
  rule isKProductionDeclaration(sort KORE_NAME:KoreName { KORE_NAMES } ATTRS)
    => true
  rule <pipeline> #visitSentence(#extractSortsFromProductions(DECLARED_SORTS), DECL)
               => #visitNext(#extractSortsFromProductions(DECLARED_SORTS), DECL .Declarations)
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
               => #forEachSentence(#extractSortsFromProductions(.Set))
                  ...
       </pipeline>
endmodule
```

