```k
requires "ekore.k"
```

```k
module KINK-CONFIGURATION
  imports EKORE-ABSTRACT
  imports SET

  syntax K ::= "#initPipeline"
```

The `<Module>` cell has to be named as such, instead
of the more natural `<module>` as K isn't able to parse the
cell name as such, instead parsing the token as the `module` keyword.

```k
  configuration <pipeline> #initPipeline </pipeline>
                <k> $PGM:Definition </k>
                <Modules>
                  <Module multiplicity="*" type="Map">
                    <name> .K </name>
                    <sorts> .Set </sorts>
                  </Module>
                </Modules>
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

`#visitSentences` and `#visit` carries the visitor, and the name of the module
it's recursing.

```k
  syntax Visitor

  syntax K ::= #visitDefintion(Visitor)
             | #visitModules(Visitor, Modules)
             | #visitSentences(Visitor, KoreName, Declarations)

  syntax K ::= #visitModule(Visitor, Module)

  rule <pipeline> #visitDefintion(VISITOR) => #visitModules(VISITOR, MODULES) ... </pipeline>
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

  syntax K ::= #visit(Visitor, KoreName, Declaration)

  rule <pipeline> #visitSentences(VISITOR, KoreName, DECL DECLS)
               => #visit(VISITOR, KoreName, DECL)
                  ~> #visitSentences(VISITOR, KoreName, DECLS)
                  ...
       </pipeline>

  rule <pipeline> #visitSentences(VISITOR, _, .Declarations)
               => .K
                  ...
       </pipeline>
```

The following construct a transformed module and place
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
                   </Module>
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
```

We first collect all sorts that have already been declared in the definition.

```k
  syntax Visitor ::= "#collectDeclaredSorts"

  rule <pipeline> #visit( #collectDeclaredSorts
                        , MNAME
                        , sort KORE_NAME { KORE_NAMES } ATTRS
                        )
              =>  (sort KORE_NAME { KORE_NAMES } ATTRS .Declarations)
                  ...
       </pipeline>
       <Modules>
         <Module>
           <name> MNAME </name>
           <sorts> ... (.Set => SetItem(KORE_NAME)) ... </sorts>
           ...
         </Module>
       </Modules>

  rule <pipeline> #visit( #collectDeclaredSorts
                        , MNAME
                        , DECL
                        )
              =>  (DECL .Declarations)
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

```k
module KINK
  imports K-MODULE-TO-KORE-MODULE
  imports EXTRACT-SORTS-FROM-PRODUCTIONS

  rule <pipeline> #initPipeline
               =>    #frontendModulesToKoreModules
                  ~> #visitDefintion(#collectDeclaredSorts)
                  ~> #visitDefintion(#extractSortsFromProductions)
                  ...
       </pipeline>
endmodule
```

