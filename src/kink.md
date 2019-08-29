```k
requires "ekore.k"
requires "file-util.k"
requires "parser-util.k"
requires "command-line.k"
```

Syntax
======

We bypass K5 parsing to use k-lights. This is because K-light allows returning
bubbles.

```k
module KINK-SYNTAX
  syntax Any ::= r"([\\n\\r]|.)*" [token]
endmodule
```

Configuration & Main Module
===========================

```k
module KINK-CONFIGURATION
  imports COMMAND-LINE-SYNTAX
  imports EKORE-ABSTRACT
  imports SET
  imports STRING-SYNTAX
  imports DEFAULT-STRATEGY

  syntax Any
  syntax Pgm ::= Any
  syntax Declaration ::= "nullDecl"
  syntax DeclCellSet
  syntax DeclarationsCellFragment

  configuration <k> #parseCommandLine($COMMANDLINE:CommandLine, $PGM:Any) </k>
                <definition>
                   <defnAttrs format="[ %2 ]%n"> .Patterns </defnAttrs>
                   <modules format="%2%n">
                     <mod format="module %2%i%n%4%n%5%n%6%n%d%n %i%dendmodule %3%n%n"
                          multiplicity="*" type="Set">
                       <name format="%2"> #token("UNNAMED", "ModuleName"):ModuleName </name>
                       <attributes format="[ %2 ]"> .Patterns </attributes>
                       <declarations format="%2">
                         <decl format="%2%n" multiplicity="*" type="Set"> nullDecl </decl>
                       </declarations>
                       <parserGenerator>
                         <prgGrammar> .Set </prgGrammar> // place to collect the grammar used to parse programs
                         <configGrammar> .Set </configGrammar> // place to collect the grammar used to parse configurations
                         <ruleGrammar> .Set </ruleGrammar> // place to collect the grammar used to parse rules
                       </parserGenerator>
                     </mod>
                   </modules>
                   <configInfo>
                     <cellName> .Map </cellName>
                     <collected> .Set </collected>
                   </configInfo>
                </definition>
                <exit-code exit=""> 1 </exit-code>
                initSCell(.Map)
                <kinkDeployedDir> token2String($KINKDEPLOYEDDIR:Path) </kinkDeployedDir>

endmodule
```

```k
module KINK
  import COMMAND-LINE
endmodule
```

Meta functions
==============

```k
module KORE-HELPERS
  imports KORE-ABSTRACT
  imports K-EQUAL
  imports STRING

  syntax Declarations ::= Declarations "++Declarations" Declarations [function]
  rule (D1 DS1) ++Declarations DS2 => D1 (DS1 ++Declarations DS2)
  rule .Declarations ++Declarations DS2 => DS2

  syntax Modules ::= Modules "++Modules" Modules [function]
  rule (M1 MS1) ++Modules MS2 => M1 (MS1 ++Modules MS2)
  rule .Modules ++Modules MS2 => MS2

  syntax Sorts ::= Sorts "++Sorts" Sorts [function]
  rule (S1, SS1) ++Sorts SS2 => S1, (SS1 ++Sorts SS2)
  rule .Sorts ++Sorts SS2 => SS2

  syntax Bool ::= Pattern "inPatterns" Patterns                      [function]
  rule (P inPatterns           .Patterns) => false
  rule (P inPatterns P:Pattern  ,  PS)    => true
  rule (P inPatterns P1:Pattern ,  PS)
    => (P inPatterns               PS)
    requires notBool P ==K P1
    
  syntax EKoreKString ::= String2EKoreKString (String) [function, functional, hook(STRING.string2token)]
  syntax TagContents  ::= String2TagContents  (String) [function, functional, hook(STRING.string2token)]
endmodule
```

-   TODO: Recurse into imported modules

```k
module META-ACCESSORS
  imports KINK-CONFIGURATION
  imports KORE-HELPERS
  imports BOOL
  imports SET

  syntax Set ::= #getImportedModules(ModuleName)      [function]
  syntax Set ::= #getImportedModulesSet(ModuleName, Set) [function]
  rule #getImportedModules(MNAME) => #getImportedModulesSet(MNAME, SetItem(MNAME))
  rule [[ #getImportedModulesSet(MNAME, MODS)
       => #getImportedModulesSet(MNAME, MODS SetItem(IMPORTED) #getImportedModules(IMPORTED))
       ]]
       <name> MNAME </name>
       <decl> koreImport(IMPORTED, _) </decl>
    requires notBool IMPORTED in MODS
  rule #getImportedModulesSet(MNAME, MODS) => MODS [owise]
  
  syntax Set ::= #getLocalProds(ModuleName)      [function]
  syntax Set ::= #getLocalProdsSet(ModuleName, Set) [function]
  rule #getLocalProds(MNAME) => #getLocalProdsSet(MNAME, .Set)
  rule [[ #getLocalProdsSet(MNAME, PRODS)
       => #getLocalProdsSet(MNAME, PRODS SetItem(PRD))
       ]]
       <name> MNAME </name>
       <decl> kSyntaxProduction(_, _) #as PRD </decl>
    requires notBool PRD in PRODS
  rule #getLocalProdsSet(MNAME, PRODS) => PRODS [owise]
  
  syntax Set ::= #getAllProds(ModuleName)      [function]
  syntax Set ::= #getAllProdsSet(Set) [function]
  rule #getAllProds(MName) => #getAllProdsSet(#getImportedModules(MName))
  rule #getAllProdsSet(SetItem(MName) Rest) => #getLocalProds(MName) #getAllProdsSet(Rest)
  rule #getAllProdsSet(.Set) => .Set
```

```k
  syntax Bool ::= #isSortDeclaredMod(ModuleName, SortName) [function]
  rule [[ #isSortDeclaredMod(MNAME:ModuleName, SORT:SortName) => true ]]
       <name> MNAME </name>
       <decl> sort SORT { PARAMS } ATTRS </decl>
  rule #isSortDeclaredMod(_, _) => false [owise]

  syntax Bool ::= #isSortDeclared(ModuleName, SortName) [function]
  syntax Bool ::= #isSortDeclaredSet(Set, SortName)     [function]
  rule #isSortDeclared(MNAME, SNAME)
    => #isSortDeclaredSet(#getImportedModules(MNAME), SNAME)
  rule #isSortDeclaredSet(SetItem(M) Ms, SNAME)
    => #isSortDeclaredMod(M, SNAME) orBool #isSortDeclaredSet(Ms, SNAME)
  rule #isSortDeclaredSet(.Set, SNAME) => false
```

```k
  syntax Bool ::= #isSymbolDeclaredMod(ModuleName, SymbolName) [function]
  rule [[ #isSymbolDeclaredMod(MNAME, SYMBOL) => true ]]
       <name> MNAME </name>
       <decl> (symbol SYMBOL { _ } ( _ ) : _ ATTRS) </decl>
  rule #isSymbolDeclaredMod(_, _) => false [owise]

  syntax Bool ::= #isSymbolDeclared(ModuleName, SymbolName) [function]
  syntax Bool ::= #isSymbolDeclaredSet(Set, SymbolName)     [function]
  rule #isSymbolDeclared(MNAME, SNAME)
    => #isSymbolDeclaredSet(#getImportedModules(MNAME), SNAME)
  rule #isSymbolDeclaredSet(SetItem(M) Ms, SNAME)
    => #isSymbolDeclaredMod(M, SNAME) orBool #isSymbolDeclaredSet(Ms, SNAME)
  rule #isSymbolDeclaredSet(.Set, SNAME) => false
```

```k
  syntax Set ::= #getDeclaredKoreSymbolsFromDecls(Declarations)         [function]
  rule #getDeclaredKoreSymbolsFromDecls
           ( (symbol SYMBOL_NAME { SORT_PARAM } ( SORT_ARGS ) : SORT ATTRS):Declaration
             DECLS
           )
    => SetItem(SYMBOL_NAME) #getDeclaredKoreSymbolsFromDecls(DECLS)
  rule #getDeclaredKoreSymbolsFromDecls(.Declarations)
    => .Set
  rule #getDeclaredKoreSymbolsFromDecls(DECL DECLS)
    => #getDeclaredKoreSymbolsFromDecls(DECLS)
       [owise]
```

```k
  syntax Sort ::= #getReturnSort(ModuleName, SymbolName) [function, withConfig]
  rule [[ #getReturnSort(MNAME, SNAME) => SORT ]]
       <name> MNAME </name>
       <decl> (symbol SNAME { .Sorts } ( _ ) : SORT ATTRS) </decl>
```

```k
  syntax Bool ::= #isFunctionSymbol(ModuleName, SymbolName) [function, withConfig]
  rule [[ #isFunctionSymbol(MNAME, SNAME) => true ]]
       <name> MNAME </name>
       <decl> symbol SNAME { .Sorts } ( _ ) : SORT [ function { .Sorts } ( .Patterns ), ATTRS ]
       </decl>
  rule [[ #isFunctionSymbol(MNAME, SNAME) => false ]]
       <name> MNAME </name>
       <decl> symbol SNAME { .Sorts } ( _ ) : SORT [ ATTRS ]
       </decl>
       [owise]
```

```k
  syntax Bool ::= #keyInAttributes(KEY, AttrList) [function]
  rule #keyInAttributes(_, .AttrList) => false
  rule #keyInAttributes(KEY, (tagSimple(KEY), _)) => true
  rule #keyInAttributes(KEY, (tagContent(KEY, _), _)) => true
  rule #keyInAttributes(KEY, (_ , REST))
    => #keyInAttributes(KEY, REST) [owise]

  syntax TagContents ::= #getAttributeContent(KEY, AttrList) [function]
//  rule #getAttributeContent(_, .AttrList) => undefined
//  rule #getAttributeContent(KEY, (tagSimple(KEY)    , _)) => undefined
  rule #getAttributeContent(KEY, (tagContent(KEY, CONTENT), _)) => CONTENT
  rule #getAttributeContent(KEY, (_ , REST))
    => #getAttributeContent(KEY, REST) [owise]
```

```k
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
  imports STRING-SYNTAX

  syntax KItem ::= "#defnToConfig"
  rule <k> (PGM:Definition ~> #defnToConfig)
          => (#defnToConfig ~> PGM)
             ...
       </k>
```

Convert K definitions to kore definitions:

```k
  rule <k> #defnToConfig
        ~> ( kDefinition(.KRequireList, MODS)
          => koreDefinition([.Patterns], MODS)
           )
           ...
       </k>
```

Convert K Import statements to Kore import statements:

```k
  rule <k> #defnToConfig
        ~> koreDefinition( _
                         , (kModule(MNAME, ATTS, IMPORTS kImport(I), DECLS) MODS)
                        => (kModule(MNAME, ATTS, IMPORTS, koreImport(I, koreAttributes(.Patterns)) DECLS) MODS)
                         )
           ...
       </k>
```

Convert K modules to kore modules:

```k
  rule <k> #defnToConfig
        ~> koreDefinition(_
                         , ( kModule(MNAME, noAtt, .KImportList, DECLS)
                          => koreModule(MNAME, DECLS, [.Patterns])
                           )
                           MODS
                         )
           ...
       </k>
```

Move Kore modules to configuration cell:

```k
  rule <k> #defnToConfig
        ~> ( koreDefinition(DEFATTRS, (koreModule(MNAME, DECLS, [ATTS]) MODS):Modules)
          => koreModule(MNAME, DECLS, [ATTS]) ~> koreDefinition(DEFATTRS, MODS)
           )
           ...
       </k>
       <modules>
         (  .Bag
         => <mod>
              <name> MNAME </name>
              <attributes> ATTS </attributes>
              ...
            </mod>
         )
         ...
       </modules>
```

Remove empty kore definitions:

```k
  rule <k> #defnToConfig ~> koreDefinition([.Patterns], .Modules)
        => .K
           ...
       </k>
```

```k
  rule <k> #defnToConfig ~> koreModule(MNAME, DECL DECLS:Declarations => DECLS, _) ... </k>
       <name> MNAME </name>
       <declarations> .Bag => <decl> DECL </decl> ... </declarations>
  rule <k> #defnToConfig ~> (koreModule(MNAME, .Declarations, _) => .K)... </k>
```

```k
endmodule
```

Below, in the "Main Module" section, we import this module and add this
transform to the `#ekorePipeline` function.

Flatten Productions
-------------------

Convert productions of the form:

```
    syntax Foo ::= "bar"
                 | "buzz"
                 > "gizmo"
```

into productions fo the form:

```
    syntax Foo ::= "bar"
    syntax Foo ::= "buzz"
    syntax Foo ::= "gizmo"
```

TODO: Add `prec()` attributes.

```k
module FLATTEN-PRODUCTIONS
  imports KINK-CONFIGURATION
  syntax KItem ::= "#flattenProductions"

  rule <k> #flattenProductions ... </k>
       <mod>
       <declarations>
          <decl> kSyntaxProduction(SORT, P1 > _:AssocAttribute P2) </decl>
       => <decl> kSyntaxProduction(SORT, P1) </decl>
          <decl> kSyntaxProduction(SORT, P2) </decl>
          ...
       </declarations>
       ...
       </mod>
  rule <k> #flattenProductions ... </k>
       <mod>
       <declarations>
          <decl> kSyntaxProduction(SORT, P1 | P2) </decl>
       => <decl> kSyntaxProduction(SORT, P1) </decl>
          <decl> kSyntaxProduction(SORT, P2) </decl>
          ...
       </declarations>
       ...
       </mod>

  rule <k> #flattenProductions => .K ... </k>
       <s> #STUCK() => .K ... </s>
endmodule
```

Extract sorts from productions
------------------------------

This transformation is a typical `MapTransform`. It adds `sort` declarations for
each production.

```k
module PRODUCTIONS-TO-SORT-DECLARATIONS
  imports META-ACCESSORS
```

If the `Declaration` was not previously declared and is a `SyntaxDeclaration`
we map to a new kore `sort` declaration. We also keep the old declaration `DECL` around:

```k
  syntax KItem ::= "#productionsToSortDeclarations"
  rule <k>  #productionsToSortDeclarations ... </k>
       <name> MNAME </name>
       <declarations>
         ( .Bag =>
           <decl> sort SORT { .Sorts } [ .Patterns ] </decl>
         )
         <decl> kSyntaxProduction(SORT, _) </decl>
         ...
       </declarations>
    requires notBool(#isSortDeclared(MNAME, SORT))
  rule <k> #productionsToSortDeclarations => .K ... </k>
       <s> #STUCK() => .K ... </s>
```

```k
endmodule
```

Once this module is defined, we import it into the main `KINK` module and
add it to the pipeline.

Make non function productions constructors
------------------------------------------

If productions are not marked as functions, we consider them constructors.

```k
module NON-FUNCTIONAL-PRODUCTIONS-TO-CONSTRUCTORS
  imports META-ACCESSORS
  syntax KItem ::= "#nonFunctionProductionsToConstructors"
  rule <k> #nonFunctionProductionsToConstructors ... </k>
       <name> MNAME </name>
       <declarations>
         <decl> kSyntaxProduction(SORT, kProductionWAttr(PROD, [ ATTRS
                                                              => (tagSimple(functional)
                                                                 , tagSimple(constructor)
                                                                 , tagSimple(injective)
                                                                 , ATTRS
                                                                 )
                                                               ]
                                                        ))
         </decl>
         ...
       </declarations>
    requires notBool #keyInAttributes(constructor, ATTRS)
     andBool notBool #keyInAttributes(function, ATTRS)
  rule <k> #nonFunctionProductionsToConstructors => .K ... </k>
       <s> #STUCK() => .K ... </s>
endmodule
```

Extract symbols from productions
--------------------------------

This transformation creates Kore symbol declarations from the K productions.
Each production should provide a `klabel`, which can be used unaltered as the
symbol name. Attributes such as `function` must also be copied into the new
Kore syntax. This transformation is idempotent.

```k
module PRODUCTIONS-TO-SYMBOL-DECLARATIONS
  imports META-ACCESSORS
  imports STRING
  imports ID
  imports PARSER-UTIL

  syntax KItem ::= "#productionsToSymbolDeclarations"
  rule <k>  #productionsToSymbolDeclarations ... </k>
       <name> MNAME </name>
       <declarations>
         <decl> kSyntaxProduction(SORT, kProductionWAttr(PROD, [ ATTRS ])) </decl>
         ( .Bag
        => <decl> symbol #symbolNameFromAttrList(ATTRS)
                    { .Sorts } (#symbolArgumentsFromProduction(PROD)) : SORT { .Sorts }
                    [ #removeKlabelAttr(ATTRS) ]
           </decl>
         )
         ...
       </declarations>
    requires notBool #isSymbolDeclared(MNAME, #symbolNameFromAttrList(ATTRS))
  rule <k> #productionsToSymbolDeclarations => .K ... </k>
       <s> #STUCK() => .K ... </s>
```

`#symbolNameFromAttrList` extracts the Name to be used for a symbol from the

```k
  syntax SymbolName ::= #symbolNameFromAttrList(AttrList) [function]
  rule #symbolNameFromAttrList(ATTRS)
    => {parseSymbolName(tokenToString(#getAttributeContent(klabel, ATTRS)))}:>SymbolName

  syntax Patterns ::= #removeKlabelAttr(AttrList) [function]
  rule #removeKlabelAttr(consAttrList(tagContent(klabel, _), ATTRS))
    => #attrList2Patterns(ATTRS)
  rule #removeKlabelAttr(consAttrList(ATTRS, ATTR))
    => #attr2Pattern(ATTRS), #removeKlabelAttr(ATTR) [owise]
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

`#symbolArgumentsFromProduction` extracts a list of kore sorts for an ekore production.

```k
  syntax Sorts ::= #symbolArgumentsFromProduction(KProduction) [function]
  rule #symbolArgumentsFromProduction(PRODITEM:KProductionItem)
    => #sortsFromProdItem(PRODITEM)
  rule #symbolArgumentsFromProduction(kProduction(PRODITEM, PROD))
    => #sortsFromProdItem(PRODITEM) ++Sorts #symbolArgumentsFromProduction(PROD)

  syntax Sorts ::= #sortsFromProdItem(KProductionItem) [function]
  rule #sortsFromProdItem(nonTerminal(KSORT:UpperName))
    => KSORT { .Sorts } , .Sorts
  rule #sortsFromProdItem(_) => .Sorts [owise]
```

```k
endmodule
```

Translate Function Rules
------------------------

`#translateRules` generates new kore axioms for rules. When the left-hand-side
of the rule is a function symbol, we generate an axiom that uses equalities.
Otherwise, if it has a constructor attribute, we generate one with rewrites. We
do not handle `requires` and `ensures` clauses yet.

```k
module TRANSLATE-FUNCTION-RULES
  imports KINK-CONFIGURATION
  imports META-ACCESSORS

  syntax KItem ::= "#translateRules"
  rule <k> #translateRules ... </k>
       <name> MNAME </name>
       <decl> kRule(noAttrs(krewrite( SYMBOL { .Sorts } ( ARG_PATTERNS ) #as LHS, RHS)))
           => axiom { #token("R", "UpperName") , .Sorts }
                \equals { #getReturnSort(MNAME, SYMBOL), #token("R", "UpperName") }
                ( LHS , RHS )
         [ .Patterns ]
       </decl>
    requires #isFunctionSymbol(MNAME, SYMBOL)

  rule <k> #translateRules ... </k>
       <name> MNAME </name>
       <decl> kRule(noAttrs(krewrite( SYMBOL { .Sorts } ( ARG_PATTERNS ) #as LHS , RHS)))
           => #fun( RETSORT
                 => axiom { .Sorts } \rewrites { RETSORT }
                        ( \and { RETSORT } (\top{ RETSORT }(), LHS)
                        , \and { RETSORT } (\top{ RETSORT }(), RHS)
                        )
                    [ .Patterns ]
                  ) (#getReturnSort(MNAME, SYMBOL))
       </decl>
    requires notBool #isFunctionSymbol(MNAME, SYMBOL)

  rule <k> #translateRules => .K ... </k>
       <s> #STUCK() => .K ... </s>
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
  imports BOOL

  syntax KItem ::= "#filterKoreDeclarations"
  rule <k> #filterKoreDeclarations ... </k>
       <declarations> ( <decl> DECL </decl> => .Bag ) ... </declarations>
    requires notBool isKoreDeclaration(DECL)
  rule <k> #filterKoreDeclarations => .K ... </k>
       <s> #STUCK() => .K ... </s>
endmodule
```
