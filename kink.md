```k
requires "ekore.k"
```

```k
module KINK-CONFIGURATION
  imports EKORE-ABSTRACT
  imports SET
```

```k
  syntax K ::= "#initPipeline"
```

Note the capital "M" in `<Modules>` and `<Module>` to work around parsing issues.

```k
  configuration <pipeline> #initPipeline </pipeline>
                <k> $PGM:Definition </k>
                <Modules>
                  <Module multiplicity="*" type="Map">
                    <name> .K </name>
                    <sorts> .Set </sorts>
                    <symbols> .Set </symbols>
                  </Module>
                </Modules>
endmodule
```

Visitor Infrastructure
----------------------

```k
module KINK-VISITORS
  imports KINK-CONFIGURATION
  imports KORE-HELPERS

  syntax Visitor
  syntax K ::= #visitDefinition(Visitor)
             | #visit(Visitor, KoreName, Declaration)
```

Many transformations may be implemented via the visitor pattern. We expect each
of these transformations to be implemented via the `#visitDefinition` construct.
`#visitDefinition` takes a `Visitor`, and iterates through every sentence in
every module. As it iterates, it places
`#visit(VISITOR, MODULE_NAME, DECLARATION)` at the top of the `<pipeline>` cell.
Each `Visitor` is expected to implement a set of rules that processes
`DECLARATION` and optionally places a `Declarations` list at the top of the
pipeline cell. The infrastucture replaces this list back into the module at the
same position. Typically, while implmenting a transformation
`#visitDefinition(#myVisitor)` would be added to the `#initPipeline` construct
defined in the `KINK` module. If a visitor needs to keep track of state, this
would be done by updating the configuration while processing
`#visit(#myVisitor, ...)`. **For a concrete example, see the "Collect declared
sorts" section.**

Below is the implementation of this infrastructure.

```k
  syntax K ::= #visitModules(Visitor, Modules)
             | #visitModule(Visitor, Module)
             | #visitSentences(Visitor, KoreName, Declarations)
  rule <pipeline> #visitDefinition(VISITOR) => #visitModules(VISITOR, MODULES) ... </pipeline>
       <k> koreDefinition(ATTR, MODULES) => koreDefinition(ATTR, .Modules) </k>
  rule <pipeline> #visitModules(VISITOR, M MS)
               =>    #visitModule(VISITOR, M)
                  ~> #visitModules(VISITOR, MS)
                  ...
       </pipeline>
  rule <pipeline> #visitModules(VISITOR, .Modules) => .K ... </pipeline>
  rule <pipeline> #visitModule(VISITOR, koreModule(MNAME, DECLS, ATTRS))
               =>    #visitSentences(VISITOR, MNAME, DECLS)
                  ~> .Declarations
                  ~> koreModule(MNAME, .Declarations, ATTRS)
                  ...
       </pipeline>
  rule <pipeline> #visitSentences(VISITOR, KoreName, DECL DECLS)
               =>    #visit(VISITOR, KoreName, DECL)
                  ~> #visitSentences(VISITOR, KoreName, DECLS)
                  ...
       </pipeline>
  rule <pipeline> #visitSentences(VISITOR, _, .Declarations)
               => .K
                  ...
       </pipeline>
```

The following constructs a transformed module and places
it back into the `<pipeline>` cell.

```k
  rule <pipeline> DECLS1 ~> #visitSentences(VA, MNAME, DECLS) ~> DECLS2
               => #visitSentences(VA, MNAME, DECLS) ~> DECLS2 ++Declarations DECLS1
                  ...
       </pipeline>

  rule <pipeline> DECLS:Declarations ~> koreModule(MNAME, .Declarations, MATTR)
               => .K
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
       <Modules> ( .Bag
                => <Module>
                    <name> MNAME </name>
                    <sorts> .Set </sorts>
                    <symbols> .Set </symbols>
                   </Module>
                 )
        ...
       </Modules>
```

If ekore defintion is already a kore definition, then ignore the conversion, but
populate the configuration.

```k
  rule <pipeline> #frontendModulesToKoreModules => .K
                  ...
       </pipeline>
       <k> koreDefinition(ATTRS, MODS)
        => #toKoreModules(MODS) ~> koreDefinition(ATTRS, .Modules)
       </k>

  rule <k>    koreModule(MNAME, DECLS:Declarations, ATTRS)
           ~> #toKoreModules(MODULES)
           ~> koreDefinition([ .Patterns ], PROCESSED_MODULES:Modules)
        =>    #toKoreModules(MODULES)
           ~> koreDefinition( [ .Patterns ]
                            ,  PROCESSED_MODULES ++Modules (koreModule(MNAME, DECLS, ATTRS) .Modules)
                            )
           ...
       </k>
       <Modules> ( .Bag
                => <Module>
                    <name> MNAME </name>
                    <sorts> .Set </sorts>
                    <symbols> .Set </symbols>
                   </Module>
                 )
        ...
       </Modules>
endmodule
```

Collect declared sorts
----------------------

This transformation collects a set of sorts declared in each module via the kore
sort declaration. For each transformation we define a module with the same name:

```k
module COLLECT-DECLARED-SORTS
```

and import the visitor infrastructure:

```k
  imports KINK-VISITORS
```

We then define a visitor and specify its behaviour:

```k
  syntax Visitor ::= "#collectDeclaredSorts"
```

When `#visit`ing a Kore sort declaration, we add that sort to the list of
declared sorts for that module. Since we want to replace the declaration
unchanged into the original module, `#visit` "returns" the same sort
declaration.

```k
  rule <pipeline> #visit( #collectDeclaredSorts
                        , MNAME
                        , sort SORT_NAME { SORT_PARAMS } ATTRS
                        )
              =>  (sort SORT_NAME { SORT_PARAMS } ATTRS .Declarations)
                  ...
       </pipeline>
       <Modules>
         <Module>
           <name> MNAME </name>
           <sorts> ... (.Set => SetItem(SORT_NAME)) ... </sorts>
           ...
         </Module>
       </Modules>
```

When `#visit`ing any other declaration (see side condition), we do nothing
except return the original declaration:

```k
  rule <pipeline> #visit( #collectDeclaredSorts
                        , MNAME
                        , DECL
                        )
              =>  (DECL .Declarations)
                  ...
       </pipeline>
       requires notBool isSortDeclaration(DECL)
endmodule
```

Below, in the "Main Module" section, we import this module and add this
transform to the `#initPipeline` function.

Extract sorts from productions
------------------------------

This transformation adds `sort` declarations for each production.

```k
module EXTRACT-SORTS-FROM-PRODUCTIONS
  imports KINK-VISITORS
```

`sortNameFromProdDecl` extracts the name of the sort from the `KProductionDeclaration`

```k
  syntax KoreName ::= sortNameFromProdDecl(KProductionDeclaration) [function]
  rule sortNameFromProdDecl(kSyntaxProduction(KSORT:UpperName, _)) => KSORT
```

We use the visitor infrastructure to implement the following transformation
step. In order to use the visitor infrastructure, the following steps have
to be followed -
  - The `Visitor` sort has to be extended with the pipeline step being
    implemented. For instance, we extend it with the
    `#extractSortsFromProductions` construct, corresponding the transformation
    step being implemented.
  - Implement the behavior of the `#visit` construct with the transformation
    construct from above. The result of the step must be a set of `transformed`
    sentences. The visitor infrastructure then takes care of putting the
    transformed sentences into corresponding modules and subsequently the
    transformed defintion.

```k
  syntax Visitor ::= "#extractSortsFromProductions"

  rule <pipeline>
           #visit( #extractSortsFromProductions
                 , MNAME
                 , DECL:KProductionDeclaration
                 )
        => (sort sortNameFromProdDecl(DECL) { .KoreNames } [ .Patterns ] DECL .Declarations)
           ...
       </pipeline>
       <Modules>
         <Module>
           <name> MNAME </name>
           <sorts> SORTS_SET
                => (SORTS_SET SetItem(sortNameFromProdDecl(DECL)))
           </sorts>
           ...
          </Module>
       </Modules>
       requires notBool(sortNameFromProdDecl(DECL) in SORTS_SET)
```

A sort declaration already exists, ignore:

```k
  rule <pipeline>
           #visit( #extractSortsFromProductions
                 , MNAME
                 , DECL:KProductionDeclaration
                 )
        => (DECL .Declarations)
           ...
       </pipeline>
       <Modules>
         <Module>
           <name> MNAME </name>
           <sorts> SORTS_SET </sorts>
           ...
          </Module>
       </Modules>
       requires sortNameFromProdDecl(DECL) in SORTS_SET
```

Ignore other `Declaration`s:

```k
   rule <pipeline>
            #visit( #extractSortsFromProductions
                  , MNAME
                  , DECL
                  )
         => (DECL .Declarations)
            ...
        </pipeline>
     requires notBool(isKProductionDeclaration(DECL))
endmodule
```

Collect declared symbols
----------------------

```k
module COLLECT-DECLARED-SYMBOLS
  imports KINK-VISITORS
  syntax Visitor ::= "#collectDeclaredSymbols"

  rule <pipeline> #visit( #collectDeclaredSymbols
                        , MNAME
                        , symbol SYMBOL_NAME { SORT_PARAM } ( SORT_ARGS ) : SORT ATTRS
                        )
               => symbol SYMBOL_NAME { SORT_PARAM } ( SORT_ARGS ) : SORT ATTRS
                  .Declarations
                  ...
       </pipeline>
       <Modules>
         <Module>
           <name> MNAME </name>
           <symbols> ... (.Set => SetItem(SYMBOL_NAME)) ... </symbols>
           ...
         </Module>
       </Modules>

  rule <pipeline> #visit( #collectDeclaredSymbols
                        , MNAME
                        , DECL
                        )
              =>  (DECL .Declarations)
                  ...
       </pipeline>
       requires notBool isSymbolDeclaration(DECL)
endmodule
```

Extract symbols from productions
--------------------------------

This transformation creates Kore symbol declarations from the K productions.
Each production should provide a `klabel`, which can be used unaltered as the
symbol name. Attributes such as `function` must also be copied into the new
Kore syntax. This transformation is idempotent.

```k
module EXTRACT-SYMBOLS-FROM-PRODUCTIONS
  imports KINK-VISITORS
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
              { .KoreNames } ( .Sorts ) : SORT { .Sorts }
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

`#filterDeclaredSymbols` - given a set of declared symbols as the first argument,
filter symbol declarations to avoid duplicate symbol declarations.

```k
  syntax Declarations ::= #filterDeclaredSymbols(Set, Declarations) [function]

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

  syntax Visitor ::= "#extractSymbolsFromProductions"

  rule <pipeline>
           #visit( #extractSymbolsFromProductions
                 , MNAME
                 , DECL:KProductionDeclaration
                 )
        => #filterDeclaredSymbols(SYMBOLS, #symbolDeclsFromProdDecl(DECL))
           ++Declarations DECL
           ...
       </pipeline>
       <Module>
         <name> MNAME </name>
         <symbols> SYMBOLS
                => SYMBOLS #symbolsFromSymbolDecls(#symbolDeclsFromProdDecl(DECL))
         </symbols>
         ...
       </Module>

  rule <pipeline>
           #visit( #extractSymbolsFromProductions
                 , MNAME
                 , DECL
                 )
        => DECL .Declarations
           ...
       </pipeline>
     requires notBool(isKProductionDeclaration(DECL))

endmodule
```

Main Module
===========

```k
module KINK
  imports K-MODULE-TO-KORE-MODULE
  imports COLLECT-DECLARED-SORTS
  imports COLLECT-DECLARED-SYMBOLS
  imports EXTRACT-SORTS-FROM-PRODUCTIONS
  imports EXTRACT-SYMBOLS-FROM-PRODUCTIONS

  rule <pipeline> #initPipeline
               =>    #frontendModulesToKoreModules
                  ~> #visitDefinition(#collectDeclaredSorts)
                  ~> #visitDefinition(#collectDeclaredSymbols)
                  ~> #visitDefinition(#extractSortsFromProductions)
                  ~> #visitDefinition(#extractSymbolsFromProductions)
                  ...
       </pipeline>
endmodule
```

