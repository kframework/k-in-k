```k
requires "ekore.k"
```

Configuration & Main Module
===========================

The K in K configuration has a "k" cell containing a definition, and a "pipeline" cell
containing operations that map over the definition in the K cell.

```k
module KINK-CONFIGURATION
  imports EKORE-ABSTRACT
  imports SET
  configuration <pipeline> $PIPELINE:K </pipeline>
                <k> $PGM:Definition </k>
endmodule
```

When an operation is at the top of the `<pipeline>` cell, it must transform the
declaration as needed.

```k
module KINK
  imports META-ACCESSORS
  imports FRONTEND-MODULES-TO-KORE-MODULES
  imports PRODUCTIONS-TO-SORT-DECLARATIONS
  imports PRODUCTIONS-TO-SYMBOL-DECLARATIONS
  imports REMOVE-FRONTEND-DECLARATIONS

  syntax K ::= "#ekorePipeline"
  rule <pipeline> #ekorePipeline
               =>    #frontendModulesToKoreModules
                  ~> #productionsToSortDeclarations
                  ~> #productionsToSymbolDeclarations
                  ...
       </pipeline>

  syntax K ::= "#runWithHaskellBackendPipeline"
  rule <pipeline> #runWithHaskellBackendPipeline
               =>    #ekorePipeline
                  ~> #removeFrontendDeclarations
                  ...
       </pipeline>
endmodule
```

Visitor Infrastructure
======================

```k
module KINK-VISITORS
  imports KINK-CONFIGURATION
  imports KORE-HELPERS
  syntax MapTransform
  rule <pipeline> T:MapTransform => .K ... </pipeline>
       <k> DEFN => T(DEFN) </k>

  syntax Definition   ::= MapTransform "(" Definition ")"                        [function]
  syntax Definition   ::= MapTransform "(" Definition "," Modules ")"            [function]
  syntax Declarations ::= MapTransform "(" Definition "," Declarations "," K ")" [function]
  syntax K ::= transformBeforeModule(MapTransform, Definition, Module)           [function]
  rule transformBeforeModule(T, DEFN, MOD) => .K                                 [owise]
  
  rule T:MapTransform (koreDefinition(ATTRS, MODULES:Modules))
    => T              (koreDefinition(ATTRS, .Modules), MODULES)
  rule T:MapTransform (koreDefinition(ATTRS, MODULES), .Modules)
    => koreDefinition(ATTRS, MODULES)

  rule T:MapTransform ( koreDefinition(DEFN_ATTRS, PROCESSED_MODULES:Modules)
                      , koreModule(MNAME, DECLS, MOD_ATTRS)
                        MODULES:Modules
                      )
    => T ( koreDefinition( DEFN_ATTRS
                         , PROCESSED_MODULES ++Modules
                           koreModule( MNAME
                                     , T ( koreDefinition(DEFN_ATTRS, PROCESSED_MODULES:Modules)
                                         , DECLS
                                         , transformBeforeModule( T
                                                                , koreDefinition(DEFN_ATTRS, PROCESSED_MODULES)
                                                                , koreModule(MNAME, DECLS, MOD_ATTRS)
                                                                )
                                         )
                                     , MOD_ATTRS
                                     )
                         )
         , MODULES
         )

  rule T:MapTransform (DEFN, .Declarations, TSTATE)
    => .Declarations
endmodule
```

Meta functions
==============

```k
module META-ACCESSORS
  imports KINK-CONFIGURATION
  imports KINK-VISITORS
  imports SET

  syntax Set ::= #getDeclaredKoreSortsFromDecls(Declarations)         [function]
  rule #getDeclaredKoreSortsFromDecls(
           (sort SORT_NAME { SORT_PARAM } ATTRS):Declaration
           DECLS
       )
    => SetItem(SORT_NAME) #getDeclaredKoreSortsFromDecls(DECLS)
  rule #getDeclaredKoreSortsFromDecls(.Declarations) => .Set
  rule #getDeclaredKoreSortsFromDecls(DECL DECLS)
    => #getDeclaredKoreSortsFromDecls(DECLS)
       [owise]


  // TODO: Recurse into imported modules
  syntax Set ::= #getDeclaredKoreSymbolsFromDecls(Declarations)         [function]
  rule #getDeclaredKoreSymbolsFromDecls(
           (symbol SYMBOL_NAME { SORT_PARAM } ( SORT_ARGS ) : SORT ATTRS):Declaration
           DECLS
       )
    => SetItem(SYMBOL_NAME) #getDeclaredKoreSymbolsFromDecls(DECLS)
  rule #getDeclaredKoreSymbolsFromDecls(.Declarations)
    => .Set
  rule #getDeclaredKoreSymbolsFromDecls(DECL DECLS)
    => #getDeclaredKoreSymbolsFromDecls(DECLS)
       [owise]
endmodule
```

Transforms
==========

K (frontend) modules to Kore Modules
------------------------------------

Since the visitor infrastructure only works over Kore modules and definitions,
frontend modules must be converted to kore modules first.

TODO: This needs to convert the modules into a topological order and check for cycles.

```k
module FRONTEND-MODULES-TO-KORE-MODULES
  imports KINK-CONFIGURATION
  imports KORE-HELPERS

  syntax K ::= "#frontendModulesToKoreModules"
  syntax Modules ::= #toKoreModules(Modules) [function]

  rule <pipeline> #frontendModulesToKoreModules => .K
                  ...
       </pipeline>
       <k> kDefinition(_:KRequireList, MODS)
        => koreDefinition([ .Patterns ], #toKoreModules(MODS))
       </k>
  rule <pipeline> #frontendModulesToKoreModules
               => .K
                  ...
       </pipeline>
       <k> koreDefinition(_, MODS:Modules => #toKoreModules(MODS)) </k>

  rule #toKoreModules(MOD:KoreModule MODS)
    => koreModules(MOD, #toKoreModules(MODS))
  rule #toKoreModules( kModule( MNAME
                              , OPT_ATTRS   // TODO: These need to be converted
                              , IMPORTS // TODO: These need to be converted
                              , DECLS
                              )
                       MS)
       => ( koreModule(MNAME, DECLS, [.Patterns])
            #toKoreModules(MS)
          ):Modules
  rule #toKoreModules(.Modules) => .Modules
```

```k
endmodule
```

Below, in the "Main Module" section, we import this module and add this
transform to the `#ekorePipeline` function.

Extract sorts from productions
------------------------------

This transformation is a typical `MapTransform`. It adds `sort` declarations for
each production.

```k
module PRODUCTIONS-TO-SORT-DECLARATIONS
  imports KINK-VISITORS
  imports META-ACCESSORS
```

Each `MapTransform` adds a symbol to the `MapTransform` sort.

```k
  syntax MapTransform ::= "#productionsToSortDeclarations"
  syntax KoreName ::= sortNameFromProdDecl(KProductionDeclaration) [function]
  rule sortNameFromProdDecl(kSyntaxProduction(KSORT:UpperName, _)) => KSORT
```

Often transforms need additional information on a per-module basis, before they
start mapping the `Declarations`. For example, in this transformation we need to
know which sorts have already been declared (so that we do not redeclare them).
In these cases, we may *(optionally)* define the `transformBeforeModule`
construct for that `MapTransform`. Note that since in Kore, a module can only
`import` a previously declared one `MapTransform` only gives access to these
modules in `DEFN`.

```k
  rule transformBeforeModule( #productionsToSortDeclarations
                            , DEFN
                            , koreModule(MNAME, DECLS, MOD_ATTRS)
                            )
    => #getDeclaredKoreSortsFromDecls(DECLS)
```

Finally, we define what the transformation does over each declaration:

* If the `Declaration` was not previously declared and is a `KProductionDeclaration`
  we map to a new kore `sort` declaration. We also keep the old declaration `DECL` around:

```k
  rule #productionsToSortDeclarations(DEFN, DECL:KProductionDeclaration DECLS, DECLARED_SORTS)
    => ( (sort sortNameFromProdDecl(DECL) { .KoreNames } [ .Patterns ])
         DECL
        .Declarations
       ) ++Declarations
       #productionsToSortDeclarations( DEFN, DECLS
                                     , DECLARED_SORTS
                                       #getDeclaredKoreSortsFromDecls(DECL)
                                     )
    requires notBool(sortNameFromProdDecl(DECL) in DECLARED_SORTS)
```

* In all other cases, this transform simply returns the original declaration unchanged:

```k
  rule #productionsToSortDeclarations(DEFN, DECL DECLS, DECLARED_SORTS)
    => DECL #productionsToSortDeclarations( DEFN, DECLS
                                          , DECLARED_SORTS
                                          )
       [owise]
```

The helper function `sortNameFromProdDecl` extracts the name of the sort from
the `KProductionDeclaration`:

```k
  syntax KoreName ::= sortNameFromProdDecl(KProductionDeclaration) [function]
  rule sortNameFromProdDecl(kSyntaxProduction(KSORT:UpperName, _)) => KSORT
```

An alternate definition of `sortNameFromProdDecl` below, is needed for programs
who's kore is generated via the java frontend:

```commented
  rule sortNameFromProdDecl(kSyntaxProduction(KSORT:UpperName, _))
    => {#parseToken("UpperName", "Sort" +String UpperName2String(KSORT))}:>UpperName
  syntax String ::= UpperName2String(UpperName) [function, hook(STRING.token2string)]
```

```k
endmodule
```

Once this module is defined, we import it into the main `KINK` module and
add it to the pipeline.

Extract symbols from productions
--------------------------------

This transformation creates Kore symbol declarations from the K productions.
Each production should provide a `klabel`, which can be used unaltered as the
symbol name. Attributes such as `function` must also be copied into the new
Kore syntax. This transformation is idempotent.

```k
module PRODUCTIONS-TO-SYMBOL-DECLARATIONS
  imports KINK-VISITORS
  imports META-ACCESSORS
```

Generic recursion that we'd like to factor out:

```k
  syntax MapTransform ::= "#productionsToSymbolDeclarations"
  rule transformBeforeModule( #productionsToSymbolDeclarations
                            , DEFN
                            , koreModule(MNAME, DECLS, MOD_ATTRS)
                            )
    => #getDeclaredKoreSymbolsFromDecls(DECLS)

  rule #productionsToSymbolDeclarations(DEFN, DECL DECLS, DECLARED_SYMBOLS)
    => DECL #productionsToSymbolDeclarations( DEFN, DECLS
                                            , DECLARED_SYMBOLS
                                            )
       [owise]

  rule #productionsToSymbolDeclarations(DEFN, DECL:KProductionDeclaration DECLS, DECLARED_SYMBOLS)
    => #filterDeclaredSymbols(DECLARED_SYMBOLS, #symbolDeclsFromProdDecl(DECL))
       ++Declarations
       DECL #productionsToSymbolDeclarations( DEFN, DECLS
                                       , DECLARED_SYMBOLS
                                         #getDeclaredKoreSymbolsFromDecls(#symbolDeclsFromProdDecl(DECL))
                                       )
```

`#symbolDeclsFromProdDecls` extracts a Kore symbol declaration,
given an E-Kore frontend production declaration.

```k
  syntax Declarations ::= #symbolDeclsFromProdDecl(KProductionDeclaration) [function]

  rule #symbolDeclsFromProdDecl(kSyntaxProduction(KSORT:UpperName, PSEQBLOCK))
    => #symbolDeclsFromPSeqBlock(KSORT, PSEQBLOCK)

  syntax Declarations ::= #symbolDeclsFromPSeqBlock(KoreName, PrioritySeqBlock) [function]

  rule #symbolDeclsFromPSeqBlock(SORT, prioritySeqBlock(PSEQBLOCK, _, PRODBLOCK))
    => #symbolDeclsFromPSeqBlock(SORT, PSEQBLOCK)
       ++Declarations #symbolDeclsFromProdBlock(SORT, PRODBLOCK)

  rule #symbolDeclsFromPSeqBlock(SORT, PRODBLOCK:ProdBlock)
    => #symbolDeclsFromProdBlock(SORT, PRODBLOCK)

  syntax Declarations ::= #symbolDeclsFromProdBlock(KoreName, ProdBlock) [function]

  rule #symbolDeclsFromProdBlock(SORT, prodBlock(PRODBLOCK, PRODWATTR))
    => #symbolDeclsFromProdBlock(SORT, PRODBLOCK)
       ++Declarations #symbolDeclsFromProdWAttr(SORT, PRODWATTR)

  rule #symbolDeclsFromProdBlock(SORT, PRODWATTR:KProductionWAttr)
    => #symbolDeclsFromProdWAttr(SORT, PRODWATTR)

  syntax Declarations ::= #symbolDeclsFromProdWAttr(KoreName, KProductionWAttr) [function]

  rule #symbolDeclsFromProdWAttr(SORT, kProductionWAttr(PROD, [ ATTRS ]))
    => symbol #symbolNameFromAttrList(ATTRS)
              { .KoreNames } (#sortsFromProd(PROD)) : SORT { .Sorts }
              [ #removeKlabelAttr(ATTRS) ]
       .Declarations

  syntax LowerName ::= "klabel" [token]
```

`#symbolNameFromAttrList` extracts the Name to be used for a symbol from the

```k
  syntax KoreName ::= #symbolNameFromAttrList(AttrList) [function]

  rule #symbolNameFromAttrList(kAttributesList(tagContent(klabel, tagContents(SNAME, _)), ATTRS))
    => SNAME

  rule #symbolNameFromAttrList(kAttributesList(_, ATTRS))
    => #symbolNameFromAttrList(ATTRS) [owise]

  syntax Patterns ::= #removeKlabelAttr(AttrList) [function]

  rule #removeKlabelAttr(kAttributesList(tagContent(klabel, _), ATTRS))
    => #attrList2Patterns(ATTRS)

  rule #removeKlabelAttr(kAttributesList(ATTR, ATTRS))
    => #attr2Pattern(ATTR), #removeKlabelAttr(ATTRS) [owise]

  rule #removeKlabelAttr(.AttrList) => .Patterns
```

`#attr2Pattern` takes an E Kore attribute, and encodes it as a kore pattern.

```k
  syntax Pattern ::= #attr2Pattern(Attr) [function]

  rule #attr2Pattern(tagSimple(KEY:LowerName))
    => KEY { .Sorts } ( .Patterns )

  syntax Patterns ::= #attrList2Patterns(AttrList) [function]

  rule #attrList2Patterns(ATTR, ATTRS) => #attr2Pattern(ATTR), #attrList2Patterns(ATTRS)
  rule #attrList2Patterns(.AttrList) => .Patterns
```

`#sortsFromProd` extracts a list of kore sorts for an ekore production.

```k
  syntax Sorts ::= #sortsFromProd(KProduction) [function]

  rule #sortsFromProd(PRODITEM:KProductionItem)
    => #sortsFromProdItem(PRODITEM)

  rule #sortsFromProd(kProduction(PROD, PRODITEM))
    => #sortsFromProd(PROD) ++Sorts #sortsFromProdItem(PRODITEM)

  syntax Sorts ::= #sortsFromProdItem(KProductionItem) [function]

  rule #sortsFromProdItem(nonTerminal(KSORT:UpperName))
    => KSORT { .Sorts } , .Sorts

  rule #sortsFromProdItem(_) => .Sorts [owise]

  syntax Sorts ::= #sortsFromKSortList(KSortList) [function]

  rule #sortsFromKSortList(KSORTS, KSORT:UpperName)
    => #sortsFromKSortList(KSORTS) ++Sorts (KSORT, .Sorts)
  rule #sortsFromKSortList(KSORT:UpperName)
    => KSORT

  syntax Declarations ::= #filterDeclaredSymbols(Set, Declarations) [function]
```

`#filterDeclaredSymbols` - given a set of declared symbols as the first argument,
filter symbol declarations to avoid duplicate symbol declarations.

```k
  rule #filterDeclaredSymbols(SYMBOLS,
          (symbol NAME { .KoreNames } ( SORTS ) : SORT ATTRS) DECLS)
    => (symbol NAME { .KoreNames } ( SORTS ) : SORT ATTRS)
       #filterDeclaredSymbols(SYMBOLS, DECLS)
    requires notBool(NAME in SYMBOLS)

  rule #filterDeclaredSymbols(SYMBOLS, (symbol NAME { _ } ( _ ) : _  _ ) DECLS)
    => #filterDeclaredSymbols(SYMBOLS, DECLS)
    requires NAME in SYMBOLS
  rule #filterDeclaredSymbols(SYMBOLS, .Declarations) => .Declarations

  syntax Set ::= #symbolsFromSymbolDecls(Declarations) [function]
  rule #symbolsFromSymbolDecls((symbol NAME { _ } ( _ ) : _ _) DECLS)
    => SetItem(NAME) #symbolsFromSymbolDecls(DECLS)
  rule #symbolsFromSymbolDecls(.Declarations) => .Set
```

```k
endmodule
```

Remove Frontend Declarations
----------------------------

Since the Haskell backend does not allow KFrontend declarations in kore, we
create a transformation that removes these. This is not loaded into the default
pipeline, just when needed for running against the Haskell backend.

```k
module REMOVE-FRONTEND-DECLARATIONS
  imports KINK-CONFIGURATION
  imports KINK-VISITORS

  syntax MapTransform ::= "#removeFrontendDeclarations"
  rule #removeFrontendDeclarations(DEFN, DECL:KFrontendDeclaration DECLS, STATE:K)
    => #removeFrontendDeclarations(DEFN, DECLS, STATE:K)
  rule #removeFrontendDeclarations(DEFN, DECL DECLS, STATE:K)
    =>  DECL
        #removeFrontendDeclarations(DEFN, DECLS, STATE:K)
        [owise]
endmodule
```
