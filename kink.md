```k
requires "ekore.k"
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
cell. When an operation is at the top of the `<pipeline>` cell, it must
transform the declaration as needed.

```k
module KINK-CONFIGURATION
  imports EKORE-ABSTRACT
  imports SET
  imports STRING-SYNTAX
  syntax Any
  configuration <pipeline> $PIPELINE:K </pipeline>
                <k> $PGM:Any </k>
                <kastProgram> "t/peano/programs/two-plus-two.peano" </kastProgram>
  syntax String ::= tokenToString(K) [function, functional, hook(STRING.token2string)]
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
  imports FRONTEND-ABSTRACT
  imports PRODUCTIONS-TO-SORT-DECLARATIONS
  imports PRODUCTIONS-TO-SYMBOL-DECLARATIONS
  imports TRANSLATE-FUNCTION-RULES
  imports REMOVE-FRONTEND-DECLARATIONS

  syntax KItem ::= "#frontendPipeline"
  rule <pipeline> #frontendPipeline
               =>    #parseOuter
                  ~> #frontendModulesToKoreModules
                  ~> #flattenProductions
                  ~> #makeGrammar("tmp/pgm-grammar.k")
                  ~> #parseProgram(FILENAME, "tmp/pgm-grammar.k")
                  ...
       </pipeline>
       <kastProgram> FILENAME </kastProgram>

  syntax KItem ::= "#ekorePipeline"
  rule <pipeline> #ekorePipeline
               =>    #parseToEKore
                  ~> #frontendModulesToKoreModules
                  ~> #flattenProductions
                  ~> #productionsToSortDeclarations
                  ~> #productionsToSymbolDeclarations
                  ~> #translateFunctionRules
                  ...
       </pipeline>

  // TODO: Why can't we just specify `-cPIPELINE=.K` from the commandline?
  syntax KItem ::= "#nullPipeline"
  rule <pipeline> #nullPipeline => .K </pipeline>

  syntax KItem ::= "#runWithHaskellBackendPipeline"
  rule <pipeline> #runWithHaskellBackendPipeline
               =>    #ekorePipeline
                  ~> #filterKoreDeclarations
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
       <k> DEFN => #mapDeclarations(T, DEFN) </k>
```

`#mapDeclarations` allows mapping a function over the declarations in a (kore)
definition:

```k
  syntax Definition ::= #mapDeclarations(MapTransform, Definition) [function]
```

Each `MapTransform` must implement the following overload. The second argument
is the `Definition` processed so far (excluding the current Module).
The third is the current Module that has been processed so far.
The fourth is the `Declaration` that needs to be processed.

```k
  syntax Declarations ::= #mapDeclarations(MapTransform, Definition, Module, Declaration) [function]
```

*Here ends the documentation for the user interface of `#mapDeclarations`*

----------------------------------------------------------------------------

`#mapDeclarations` calls a helper function that accumulates a "transformed
definition" starting with an empty definition, and processes each module in
order:

```k
  syntax Definition ::= #mapDeclarations(MapTransform, Definition, Modules) [function]
  rule #mapDeclarations(T, koreDefinition(ATTRS, UNPROCESSED_MODULES:Modules))
    => #mapDeclarations(T, koreDefinition(ATTRS, .Modules), UNPROCESSED_MODULES)

  rule #mapDeclarations
           ( T:MapTransform
           , koreDefinition(DEFN_ATTRS, PROCESSED_MODULES:Modules)
           , koreModule(MNAME, UNPROCESSED_DECLS, ATTRS) MODULES:Modules
           )
    => #mapDeclarations
           ( T
           , koreDefinition
                 ( DEFN_ATTRS
                 , PROCESSED_MODULES ++Modules
                   #mapDeclarations
                       ( T
                       , koreDefinition(DEFN_ATTRS, PROCESSED_MODULES:Modules)
                       , koreModule(MNAME, .Declarations, ATTRS)
                       , UNPROCESSED_DECLS
                       )
                   .Modules
                 )
           , MODULES
           )

  rule #mapDeclarations(T, koreDefinition(ATTRS, PROCESSED_MODULES), .Modules)
    => koreDefinition(ATTRS, PROCESSED_MODULES)
```

```k
  syntax Module ::= #mapDeclarations(MapTransform, Definition, Module, Declarations) [function]
  rule #mapDeclarations
          ( T:MapTransform
          , DEFN
          , koreModule( MNAME
                      , PROCESSED_DECLS
                      , ATTRS
                      )
          , DECL:Declaration UNPROCESSED_DECLS
          )
    => #mapDeclarations
           ( T:MapTransform
           , DEFN
           , koreModule( MNAME
                       , PROCESSED_DECLS ++Declarations
                         #mapDeclarations( T:MapTransform
                                         , DEFN
                                         , koreModule(MNAME, PROCESSED_DECLS, ATTRS)
                                         , DECL
                                         )
                       , ATTRS
                       )
           , UNPROCESSED_DECLS
           )
  rule #mapDeclarations(T:MapTransform, DEFN, MOD, .Declarations)
    => MOD
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

-   TODO: Functions defined here should be modelled after the functions in
    section 7 of the semantics of K document.
-   TODO: Recurse into imported modules

```k
module META-ACCESSORS
  imports KINK-CONFIGURATION
  imports KINK-VISITORS
  imports BOOL
  imports SET

  syntax Bool ::= #isSortDeclared(Declarations, SortName) [function]
  rule #isSortDeclared(.Declarations, _) => false
  rule #isSortDeclared( (sort SORT_NAME { SORT_PARAM } ATTRS)
                        DECLS
                      , SORT_NAME
                      )
    => true
  rule #isSortDeclared(DECL DECLS, SORT_NAME)
    => #isSortDeclared(DECLS     , SORT_NAME)
       [owise]
```

```k
  syntax Bool ::= #isSymbolDeclared(Declarations, SymbolName) [function]
  rule #isSymbolDeclared(.Declarations, _) => false
  rule #isSymbolDeclared( (symbol SYMBOL_NAME { _ } ( _ ) : _ ATTRS)
                          DECLS
                        , SYMBOL_NAME
                        )
    => true
  rule #isSymbolDeclared(DECL DECLS, SYMBOL_NAME)
    => #isSymbolDeclared(DECLS     , SYMBOL_NAME)
       [owise]
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

See Section 7.3 of Semantics of K.
TODO: This should take `Symbol`, and not `SymbolName`?

```k
  syntax Sort ::= #getReturnSort(Declarations, SymbolName) [function]
  rule #getReturnSort( (symbol SNAME { .Sorts } ( _ ) : SORT ATTRS) DECLS
                     , SNAME
                     )
    => SORT
  rule #getReturnSort(DECL DECLS, SNAME)
    => #getReturnSort(DECLS, SNAME)
       [owise]
```

TODO: I'd like something like this eventually:

```commented
  rule #getReturnSort(.Declarations, SNAME)
    => #error("Symbol " +String SNAME +String " undeclared")
       [owise]
```

```k
  syntax Bool ::= #isFunctionSymbol(Declarations, SymbolName) [function]
  rule #isFunctionSymbol
            ( ( symbol SNAME { .Sorts } ( _ ) : SORT:Sort
                             [ function { .Sorts } ( .Patterns )
                             , ATTRS:Patterns
                             ]
              ):Declaration
              DECLS
            , SNAME
            )
    => true
  rule #isFunctionSymbol(DECL DECLS, SNAME)
    => #isFunctionSymbol(DECLS, SNAME)
       [owise]

  syntax LowerName ::= "function" [token]
```

```k
endmodule
```

```k
module IO-HELPERS
  imports KINK-CONFIGURATION
  imports K-IO
  imports META

  syntax StringOrHole ::= "#hole"
                        | String
  syntax KItem ::= "#withFD" "(" IOInt ")"
                 | "#doWrite" "(" String ")"
                 | "#doClose"
                 | "#writeStringToFile" "(" StringOrHole "," String ")"
                 | "#doSystem" "(" String ")"
                 | "#doSystemGetOutput"
                 | "#doParseAST"

  rule <k> S:String ~> #writeStringToFile(#hole, FILE)
        => #writeStringToFile(S, FILE)
           ...
       </k>
  rule <k> #writeStringToFile(STRING, FILE)
        => #withFD(#open(FILE, "w")) ~> #doWrite(STRING) ~> #doClose
           ...
       </k>

  rule <k> #withFD(I:Int) ~> #doWrite(CONTENT)
        => #withFD(I) ~> #write(I, CONTENT)
           ...
       </k>

  rule <k> #withFD(I:Int) ~> #doClose
        => #close(I)
           ...
       </k>

  rule <k> #doSystem(COMMAND) => #system(COMMAND)
           ...
       </k>

  rule <k> #systemResult(0, STDOUT, STDERR) ~> #doSystemGetOutput
        => STDOUT
           ...
       </k>

  rule <k> S:String ~> #doParseAST
        => #parseAST(S)
           ...
       </k>

endmodule
```

Transforms
==========

Parse Outer
-----------

```k
module PARSE-OUTER
  imports KINK-CONFIGURATION
  imports IO-HELPERS

  syntax KItem ::= "#parseOuter"
  rule <pipeline> #parseOuter => .K ... </pipeline>
       <k> T:Any
        => #writeStringToFile(tokenToString(T), "tmp/definition")
        ~> #doSystem("k-light2k5.sh --module FRONTEND-SYNTAX --output kast .build/ekore.k Definition tmp/definition")
        ~> #doSystemGetOutput
        ~> #doParseAST
           ...
       </k>
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
  imports IO-HELPERS

  syntax KItem ::= "#makeGrammar" "(" String ")" // Grammar Filename
  syntax KItem ::= "#parseProgram" "(" String "," String ")" // Program Filename, Grammar Filename

  rule <k> DEFN
        => #writeStringToFile( "module PGM-GRAMMAR\n" +String
                               grammarToString(#getLanguageGrammar(#getAllDeclarations(DEFN))) +String
                               "endmodule\n"
                             , GRAMMAR_FILENAME
                             )
           ...
       </k>
       <pipeline> #makeGrammar(GRAMMAR_FILENAME) => .K ... </pipeline>
       
  rule <k> .K
        => #doSystem("k-light2k5.sh --output kore --module PGM-GRAMMAR "
                     +String GRAMMAR_FILENAME +String " Nat " +String PGM_FILENAME)
        ~> #doSystemGetOutput
        ~> #writeStringToFile(#hole, "tmp/pgm.kore")
        ~> #doSystem("k-light2k5.sh --output kast --module KORE-SYNTAX .build/kore.k Pattern tmp/pgm.kore")
        ~> #doSystemGetOutput
        ~> #doParseAST
           ...
       </k>
       <pipeline> #parseProgram(PGM_FILENAME, GRAMMAR_FILENAME) => .K ... </pipeline>

   syntax Declarations ::= #getAllDeclarations(Definition) [function]
   rule #getAllDeclarations(koreDefinition(ATTRS, koreModule(_, DECLS, _):Module MODULES))
     => DECLS ++Declarations #getAllDeclarations(koreDefinition(ATTRS, MODULES))
   rule #getAllDeclarations(koreDefinition(_, .Modules))
     => .Declarations

   syntax Declarations ::= #getLanguageGrammar(Declarations) [function]
   rule #getLanguageGrammar(kSyntaxProduction(S, P) DECLS)
     => kSyntaxProduction(S, P) #getLanguageGrammar(DECLS)
   rule #getLanguageGrammar(DECL DECLS)
     => #getLanguageGrammar(DECLS) [owise]
   rule #getLanguageGrammar(.Declarations)
     => .Declarations [owise]

   syntax String ::= grammarToString(Declarations) [function]
   rule grammarToString(.Declarations)
     => ""
   rule grammarToString(kSyntaxProduction(S, kProductionWAttr(P, ATTRS)) DECLS)
     => "syntax " +String tokenToString(S) +String " ::= "
                  +String KProductionToString(P) +String " "
                  +String OptionalAttributesToString(ATTRS)
        +String "\n"
        +String grammarToString(DECLS)
   rule grammarToString( kSyntaxProduction(S, TAG:Tag(KSORTLIST:KSortList) ATTRS)
                         DECLS
                       )
     => "syntax " +String tokenToString(S) +String " ::= "
                  +String tokenToString(TAG)
                  +String "(" +String KSortListToString(KSORTLIST) +String ")" +String " "
                  +String OptionalAttributesToString(ATTRS)
        +String "\n"
        +String grammarToString(DECLS)

   syntax String ::= KSortListToString(KSortList) [function]
   rule KSortListToString(S:KSort) => tokenToString(S)
   rule KSortListToString(Ss, S) => KSortListToString(Ss) +String "," +String tokenToString(S)

   syntax String ::= KProductionToString(KProduction) [function]
   rule KProductionToString(PI:KProductionItem)
     => KProductionItemToString(PI)
   rule KProductionToString(kProduction(PI, PIs))
     => KProductionItemToString(PI) +String "\n" +String KProductionToString(PIs)

   syntax String ::= KProductionItemToString(KProductionItem) [function]
   rule KProductionItemToString(nonTerminal(N)) => tokenToString(N)
   rule KProductionItemToString(terminal(T))    => tokenToString(T)
   rule KProductionItemToString(regexTerminal(R)) => "r" +String tokenToString(R)

   syntax String ::= OptionalAttributesToString(OptionalAttributes) [function]
   rule OptionalAttributesToString(noAtt) => ""
   rule OptionalAttributesToString([ ATTRLIST ])
     => "[" +String AttrListToString(ATTRLIST) +String "]"

   syntax String ::= AttrListToString(AttrList) [function]
   rule AttrListToString(.AttrList)       => "dummy"
   rule AttrListToString(ATTR, .AttrList) => AttrToString(ATTR)
   rule AttrListToString(ATTR, ATTRs)     => AttrToString(ATTR) +String "," +String AttrListToString(ATTRs)

   syntax String ::= AttrToString(Attr) [function]
   rule AttrToString(tagSimple(KEY))
     => tokenToString(KEY)
   rule AttrToString(KEY:KEY(CONTENTS:TagContents))
     => tokenToString(KEY) +String "(" +String tokenToString(CONTENTS) +String ")"
   rule AttrToString(KEY:KEY(CONTENTS:EKoreKString))
     => tokenToString(KEY) +String "(" +String tokenToString(CONTENTS) +String ")"

   syntax String ::= TagContentsToString(TagContents) [function]
   rule TagContentsToString(tagContents(TC, TCs))
     => tokenToString(TC) +String " " +String TagContentsToString(TCs)
   rule TagContentsToString(.TagContents)
     => ""
endmodule
```

Parse into EKore
----------------

```k
module PARSE-TO-EKORE
  imports EKORE-ABSTRACT
  imports KINK-CONFIGURATION
  imports IO-HELPERS
  syntax KItem ::= "#parseToEKore"

  rule <k> T:Any
        => #writeStringToFile(tokenToString(T), "tmp/definition.k")
        ~> #doSystem("k-light2k5.sh --module EKORE-SYNTAX .build/ekore.k Definition tmp/definition.k")
        ~> #doSystemGetOutput
        ~> #doParseAST
           ...
       </k>
       <pipeline> #parseToEKore => .K ... </pipeline>
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

  syntax KItem ::= "#frontendModulesToKoreModules"
  syntax Modules ::= #toKoreModules(Modules) [function]

  rule <pipeline> #frontendModulesToKoreModules => .K
                  ...
       </pipeline>
       <k> kDefinition(_:KRequireList, MODS)
        => koreDefinition([ .Patterns ], #toKoreModules(MODS))
           ...
       </k>
  rule <pipeline> #frontendModulesToKoreModules
               => .K
                  ...
       </pipeline>
       <k> koreDefinition(_, MODS:Modules => #toKoreModules(MODS)) </k>

  rule #toKoreModules(MOD:KoreModule MODS)
    => consModules(MOD, #toKoreModules(MODS))
  rule #toKoreModules
           ( kModule
                 ( MNAME
                 , OPT_ATTRS // TODO: These need to be converted
                 , IMPORTS   // TODO: These need to be converted
                 , DECLS
                 )
             MS
           )
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
  imports KINK-VISITORS
  syntax MapTransform ::= "#flattenProductions"

  rule #mapDeclarations
           ( #flattenProductions
           , DEFN
           , PROCESSED_MODULES
           , kSyntaxProduction(SORT, P:KProductionWAttr)
           )
    => kSyntaxProduction(SORT, P) .Declarations

  rule #mapDeclarations
           ( #flattenProductions
           , DEFN
           , PROCESSED_MODULES
           , kSyntaxProduction(SORT, P1 > P2)
           )
    => #mapDeclarations
           ( #flattenProductions
           , DEFN
           , PROCESSED_MODULES
           , kSyntaxProduction(SORT, P1)
           )
       ++Declarations
       #mapDeclarations
           ( #flattenProductions
           , DEFN
           , PROCESSED_MODULES
           , kSyntaxProduction(SORT, P2)
           )

  rule #mapDeclarations
           ( #flattenProductions
           , DEFN
           , PROCESSED_MODULES
           , kSyntaxProduction(SORT, P1 | P2)
           )
    => #mapDeclarations
           ( #flattenProductions
           , DEFN
           , PROCESSED_MODULES
           , kSyntaxProduction(SORT, P1)
           )
       ++Declarations
       #mapDeclarations
           ( #flattenProductions
           , DEFN
           , PROCESSED_MODULES
           , kSyntaxProduction(SORT, P2)
           )

  rule #mapDeclarations
           ( #flattenProductions
           , DEFN, MOD, DECL
           )
    => DECL .Declarations [owise]
endmodule
```

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
  syntax SortName ::= sortNameFromProdDecl(SyntaxDeclaration) [function]
  rule sortNameFromProdDecl(kSyntaxProduction(KSORT:UpperName, _)) => KSORT
```

Finally, we define what the transformation does over each declaration:

* If the `Declaration` was not previously declared and is a `SyntaxDeclaration`
  we map to a new kore `sort` declaration. We also keep the old declaration `DECL` around:

```k
  rule #mapDeclarations
           ( #productionsToSortDeclarations
           , DEFN
           , koreModule(MNAME, PROCESSED_DECLS:Declarations, ATTRS)
           , DECL:SyntaxDeclaration
           )
    => (sort sortNameFromProdDecl(DECL) { .Sorts } [ .Patterns ])
       DECL
       .Declarations
    requires notBool(#isSortDeclared(PROCESSED_DECLS, sortNameFromProdDecl(DECL)))
```

* In all other cases, this transform simply returns the original declaration unchanged:

```k
  rule #mapDeclarations
           ( #productionsToSortDeclarations
           , DEFN, MOD, DECL
           )
    => DECL .Declarations [owise]
```

The helper function `sortNameFromProdDecl` extracts the name of the sort from
the `SyntaxDeclaration`:

```k
  syntax SortName ::= sortNameFromProdDecl(SyntaxDeclaration) [function]
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
  imports STRING
  imports ID

  syntax MapTransform ::= "#productionsToSymbolDeclarations"
  rule #mapDeclarations
           ( #productionsToSymbolDeclarations
           , DEFN, MOD, DECL
           )
    => DECL .Declarations [owise]
  rule #mapDeclarations
           ( #productionsToSymbolDeclarations
           , DEFN
           , koreModule(MNAME, PROCESSED_DECLS:Declarations, MOD_ATTRS)
           , kSyntaxProduction(SORT, kProductionWAttr(PROD, [ ATTRS ]))
           )
    => symbol #symbolNameFromAttrList(ATTRS)
               { .Sorts } (#symbolArgumentsFromProduction(PROD)) : SORT { .Sorts }
               [ #removeKlabelAttr(ATTRS) ]
       kSyntaxProduction(SORT, kProductionWAttr(PROD, [ ATTRS ]))
       .Declarations
    requires notBool #isSymbolDeclared(PROCESSED_DECLS, #symbolNameFromAttrList(ATTRS))
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
    // TODO: Should allow both LowerName and UpperName
    // TODO: Do not silently allow multiple words as klabels (e.g. if the tag
    //       contents has a space in it). Really speaking we need to parse
    //       the TagContents as a SymbolName, and not just do some ad-hoc processing
    => {#parseToken("LowerName", replaceAll(tokenToString(SNAME), " ", ""))}:>LowerName
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
  imports KINK-VISITORS
  imports META-ACCESSORS

  syntax MapTransform ::= "#translateFunctionRules"
  rule #mapDeclarations( #translateFunctionRules
                       , DEFN
                       , koreModule(MNAME, PROCESSED_DECLS, ATTRS)
                       , kRule(noAttrs(krewrite( FUNC { .Sorts } ( ARG_PATTERNS ) , RHS)))
                       )
    => ( axiom   {                          #token("R", "UpperName") , .Sorts }
         \equals { #getReturnSort(PROCESSED_DECLS, FUNC), #token("R", "UpperName") }
         ( FUNC { .Sorts } ( ARG_PATTERNS ) , RHS )
         [ .Patterns ]
       ) .Declarations
    requires #isFunctionSymbol(PROCESSED_DECLS, FUNC)

  rule #mapDeclarations(#translateFunctionRules, DEFN, MOD, DECL)
    => DECL .Declarations
       [owise]
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

  syntax MapTransform ::= "#filterKoreDeclarations"
  rule #mapDeclarations
           ( #filterKoreDeclarations
           , DEFN
           , MOD
           , DECL:KoreDeclaration
           )
    => DECL .Declarations
  rule #mapDeclarations
           ( #filterKoreDeclarations
           , DEFN
           , MOD
           , DECL
           )
    => .Declarations
       [owise]
endmodule
```
