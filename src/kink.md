```k
requires "ekore.k"
requires "file-util.k"
requires "parser-util.k"
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

The K in K configuration has a "k" cell containing a definition, and a
"pipeline" cell containing operations that map over the definition in the K
cell. When an operation is at the top of the `<k>` cell, it must
transform the declaration as needed.

```k
module KINK-CONFIGURATION
  imports EKORE-ABSTRACT
  imports SET
  imports STRING-SYNTAX
  imports DEFAULT-STRATEGY

  syntax Any
  syntax Declaration ::= "nullDecl"
  syntax DeclCellSet
  syntax DeclarationsCellFragment
  configuration <k> $PGM:Any ~> $PIPELINE:K </k>
                <definition>
                   <defnAttrs format="[ %2 ]%n"> .Patterns </defnAttrs>
                   <modules format="%2%n">
                     <mod format="module %2%i%n%4%n%5%n%6%d%n %i%dendmodule %3%n%n"
                          multiplicity="*" type="Set">
                       <name format="%2"> #token("UNNAMED", "ModuleName"):ModuleName </name>
                       <attributes format="[ %2 ]"> .Patterns </attributes>
                       <imp format="%2"> .Declarations </imp>
                       <declarations format="%2">
                         <decl format="%2%n" multiplicity="*" type="Set"> nullDecl </decl>
                       </declarations>
                       <grammar> .Set </grammar>
                     </mod>
                   </modules>
                </definition>
                <s> $STRATEGY:K </s>
endmodule
```

```k
module KINK
  imports META-ACCESSORS
  imports PARSE-OUTER
  imports PARSE-PROGRAM
  imports PARSE-TO-EKORE
  imports FRONTEND-MODULES-TO-KORE-MODULES
  imports FLATTEN-PRODUCTIONS
  imports OUTER-ABSTRACT
  imports PRODUCTIONS-TO-SORT-DECLARATIONS
  imports PRODUCTIONS-TO-SYMBOL-DECLARATIONS
  imports TRANSLATE-FUNCTION-RULES
  imports REMOVE-FRONTEND-DECLARATIONS

  syntax K ::= "#kastPipeline" "(" String ")" [function]
  rule #kastPipeline(PATH)
    => #parseOuter
    ~> #defnToConfig
    ~> #flattenProductions
    ~> #collectGrammar
    ~> #parseProgramPath(PATH)

  syntax K ::= "#ekorePipeline" [function]
  rule #ekorePipeline
    => #parseToEKore
    ~> #defnToConfig
    ~> #flattenProductions
    ~> #productionsToSortDeclarations
    ~> #productionsToSymbolDeclarations
    ~> #translateFunctionRules

  // TODO: Why can't we just specify `-cPIPELINE=.K` from the commandline?
  syntax K ::= "#nullPipeline" [function]
  rule #nullPipeline => .K

  syntax K ::= "#runWithHaskellBackendPipeline" [function]
  rule #runWithHaskellBackendPipeline
    => #ekorePipeline
    ~> #filterKoreDeclarations
endmodule
```

Meta functions
==============

```k
module KORE-HELPERS
  imports KORE-ABSTRACT
  imports K-EQUAL

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
endmodule
```

-   TODO: Recurse into imported modules

```k
module META-ACCESSORS
  imports KINK-CONFIGURATION
  imports KORE-HELPERS
  imports BOOL
  imports SET

  syntax Bool ::= #isSortDeclared(ModuleName, SortName) [function, withConfig]
  rule [[ #isSortDeclared(MNAME:ModuleName, SORT:SortName) => true ]]
       <name> MNAME </name>
       <decl> sort SORT { PARAMS } ATTRS </decl>
  rule #isSortDeclared(_, _) => false [owise]
```

```k
  syntax Bool ::= #isSymbolDeclared(ModuleName, SymbolName) [function, withConfig]
  rule [[ #isSymbolDeclared(MNAME, SYMBOL) => true ]]
       <name> MNAME </name>
       <decl> (symbol SYMBOL { _ } ( _ ) : _ ATTRS) </decl>
  rule #isSymbolDeclared(_, _) => false [owise]
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
  syntax LowerName ::= "function" [token]
```

```k
endmodule
```

Transforms
==========

Parse Outer
-----------

```k
module PARSE-OUTER
  imports KINK-CONFIGURATION
  imports PARSER-UTIL
  imports META

  // TODO: remove: #writeStringToFile, #doSystem, #doSystemGetOutput, #doParseAST
  syntax KItem ::= "#parseOuter"
  rule <k> PGM:Any ~> #parseOuter => parseOuter(tokenToString(PGM)) ... </k>
endmodule
```

Parse Program
-------------

```k
module PARSE-PROGRAM
  imports KINK-CONFIGURATION
  imports K-PRODUCTION-ABSTRACT
  imports EKORE-KSTRING-ABSTRACT
  imports KORE-HELPERS
  imports STRING
  imports FILE-UTIL
  imports PARSER-UTIL
  imports META

  syntax KItem ::= "#parseProgramPath" "(" String ")" // Program Filename
                 | "#parseProgram" "(" IOString ")" // Program content
                 | "#collectGrammar"
  rule <k> #parseProgramPath(PGM_FILENAME) => #parseProgram(readFile(PGM_FILENAME)) ... </k>

  rule <k> #parseProgram(PGM)
        => parseWithProductions(GRAMMAR, "Pgm", PGM)
           ...
       </k>
       <grammar> GRAMMAR </grammar>

  rule <k> #collectGrammar ... </k>
       <decl> kSyntaxProduction(SORT, PROD) </decl>
       <grammar> (.Set => SetItem(kSyntaxProduction(SORT, PROD))) REST </grammar>
    requires notBool(kSyntaxProduction(SORT, PROD) in REST)
  rule <k> #collectGrammar => .K ... </k>
       <s> #STUCK() => .K ... </s>
endmodule
```

Parse into EKore
----------------

```k
module PARSE-TO-EKORE
  imports EKORE-ABSTRACT
  imports KINK-CONFIGURATION
  imports PARSER-UTIL
  imports META

  syntax KItem ::= "#parseToEKore"
  rule <k> PGM:Any ~> #parseToEKore => parseEKore(tokenToString(PGM)) ... </k>
endmodule
```

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
          <decl> kSyntaxProduction(SORT, P1 > P2) </decl>
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

Extract symbols from productions
--------------------------------

This transformation creates Kore symbol declarations from the K productions.
Each production should provide a `klabel`, which can be used unaltered as the
symbol name. Attributes such as `function` must also be copied into the new
Kore syntax. This transformation is idempotent.

```k
module PRODUCTIONS-TO-SYMBOL-DECLARATIONS
  imports META-ACCESSORS
  imports META
  imports STRING
  imports ID
  imports PARSER-UTIL

  syntax MapTransform ::= "#productionsToSymbolDeclarations"
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
  rule <k>  #productionsToSymbolDeclarations => .K ... </k>
       <s> #STUCK() => .K ... </s>
```

`#symbolNameFromAttrList` extracts the Name to be used for a symbol from the

```k
  syntax LowerName ::= "klabel" [token]
  syntax SymbolName ::= #symbolNameFromAttrList(AttrList) [function]
  rule #symbolNameFromAttrList
           ( consAttrList
                 ( tagContent(klabel, SNAME:TagContents)
                 , ATTRS
                 )
           )
    // TODO: We need to handle errors
    => {parseSymbolName(tokenToString(SNAME))}:>SymbolName
  rule #symbolNameFromAttrList(consAttrList(_, ATTRS))
    => #symbolNameFromAttrList(ATTRS) [owise]

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

  // TODO: This reverses the pattern list
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

`#translateFunctionRules` generates new kore axioms for rewrite rules over
function symbols. Rules whose LHS is not a kore symbol with the function
attribute should be ignored. Since the rewrite rule carries no additional
information over the kore axiom, it can be discarded.

```k
module TRANSLATE-FUNCTION-RULES
  imports KINK-CONFIGURATION
  imports META-ACCESSORS

  syntax KItem ::= "#translateFunctionRules"
  rule <k> #translateFunctionRules ... </k>
       <name> MNAME </name>
       <decl> kRule(noAttrs(krewrite( SYMBOL { .Sorts } ( ARG_PATTERNS ) , RHS)))
           => axiom { #token("R", "UpperName") , .Sorts }
                \equals { #getReturnSort(MNAME, SYMBOL), #token("R", "UpperName") }
                ( SYMBOL { .Sorts } ( ARG_PATTERNS ) , RHS )
         [ .Patterns ]
       </decl>
    requires #isFunctionSymbol(MNAME, SYMBOL)
  rule <k> #translateFunctionRules => .K ... </k>
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
