```k
requires "kore.k"

module KFRONT-SYNTAX
  imports STRING
  imports KORE-SYNTAX

  syntax KFrontDeclarations ::= List{KFrontDeclaration, ""}
  syntax KFrontDeclaration  ::= ksyntax(KFrontSort , KFrontLabel, KFrontSorts)
  syntax KFrontSort         ::= ksort(Name)
  syntax KFrontSorts        ::= List{KFrontSort, ";"} [klabel(KFrontSorts)]
  syntax KFrontLabel        ::= klabel(Name)

  syntax KFrontModule     ::=  "kmodule" Name KFrontSentences "endkmodule"
  syntax KFrontModules    ::=  List{KFrontModule, " "}                     [klabel(kauxModules)]
  syntax KFrontSentences  ::=  List{KFrontSentence, " "}                   [klabel(kauxSentences)]
  syntax KFrontSentence   ::=  KFrontDeclaration
  syntax KFrontDefinition ::=  KFrontModules
endmodule
```

```k
module KFRONT-TO-KORE
  imports KFRONT-SYNTAX
  imports KORE-HELPERS
  imports DOMAINS
 
  syntax Processed   ::=  #processedDefintion ( KFrontDefinition )

  syntax Intermdiate ::=   #initialization    ( KFrontDefinition )
                         | #sortDeclaration   ( Intermdiate )   [strict]
                         | #symbolDeclaration ( Intermdiate )   [strict]
                         |  Processed

  syntax KResult    ::= Processed
  syntax KItem      ::=  "#done"
                       | "#configurationDefinitionToTerm"

  syntax Name ::= "inj" | "From" | "To"

  configuration <T>
                  <k>
                      #symbolDeclaration(
                        #sortDeclaration(
                          #initialization( $PGM:KFrontModules )
                        )
                      ) ~> #configurationDefinitionToTerm ~> #done
                  </k>
                  <koreDefinition> .K </koreDefinition>
                  <kore>
                    <definitionAttributes> [ .Patterns ] </definitionAttributes>
                    <modules>
                      <koreModule multiplicity="*">
                        <name> .K </name>
                        <sortDeclarations> .Declarations </sortDeclarations>
                        <symbolDeclarations>
                          (symbol inj { From , To , .Names } ( From , .Sorts) : To [ .Patterns ])
                          .Declarations
                        </symbolDeclarations>
                      </koreModule>
                    </modules>
                  </kore>
                </T>

   syntax PipelineStep ::=     "Initialization"
                             | "SortsDeclaration"
                             | "SymbolsDeclaration"
   syntax Intermediate ::=     "#pipelineStepHelper" "(" PipelineStep "," KFrontDefinition "|" KFrontDefinition ")"

   rule #processedDefintion( _ ) ~> #done => #done

   rule #initialization( AUXDEF ) => #pipelineStepHelper(Initialization, .KFrontModules | AUXDEF)

   rule #pipelineStepHelper( _ ,  MODULES | .KFrontModules ) => #processedDefintion( MODULES )

   rule <k>
           (#pipelineStepHelper( Initialization, MODULE | kmodule MODULENAME KSNTNCS endkmodule MODULES)
               =>
            #pipelineStepHelper( Initialization, (kmodule MODULENAME KSNTNCS endkmodule) MODULE | MODULES))
           ...
        </k>
        <kore>
           ...
           <modules>
           ( .Bag
              =>
             <koreModule>
               <name> MODULENAME </name>
               ...
             </koreModule>)
           </modules>
       </kore>
```

Pipeline Steps
==============

Collect sort declarations:

```k
   rule #sortDeclaration( #processedDefintion( DEF ) ) => #pipelineStepHelper( SortsDeclaration, .KFrontModules | DEF )
   rule <k>
            (#pipelineStepHelper( SortsDeclaration, MODULE | kmodule NAME KSENTENCES endkmodule MODULES)
              =>
             #pipelineStepHelper( SortsDeclaration, kmodule NAME KSENTENCES endkmodule MODULE | MODULES))
           ...
       </k>
       <koreModule>
         <name>              NAME                                            </name>
         <sortDeclarations> .Declarations => #declareSorts(KSENTENCES, .Set) </sortDeclarations>
         ...
       </koreModule>

   syntax Declarations ::= #declareSorts(KFrontSentences, Set) [function]
   rule #declareSorts(.KFrontSentences, _) => .Declarations
   rule #declareSorts(ksyntax(ksort(SORT:Name), _, _) KSS, DECLARED_SORTS)
     => sort SORT { .Names } [ .Patterns ]
        #declareSorts(KSS, SetItem(SORT) DECLARED_SORTS)
     requires notBool(SORT in DECLARED_SORTS)
   rule #declareSorts(ksyntax(ksort(SORT:Name), _, _) KSS, DECLARED_SORTS)
     => #declareSorts(KSS, DECLARED_SORTS)
     requires SORT in DECLARED_SORTS
```

Collect symbol declarations

```k
   syntax Declarations ::= #declareSymbols(KFrontSentences, Declarations) [function]
                         | #declareSymbolsSentence(KFrontSentence, Declarations) [function]

// TODO: Take into account sort params. Will need to do a lookup.
   syntax Sorts ::= KFrontSorts2KoreSorts(KFrontSorts) [function]
   rule KFrontSorts2KoreSorts(.KFrontSorts)  => .Sorts
   rule KFrontSorts2KoreSorts(ksort(N) ; SS) => N { .Sorts } , KFrontSorts2KoreSorts(SS)

   rule #symbolDeclaration( #processedDefintion ( DEF )) => #pipelineStepHelper( SymbolsDeclaration, .KFrontModules | DEF )


   rule <k> #pipelineStepHelper(SymbolsDeclaration, MODULE | kmodule NAME KSENTENCES endkmodule MODULES)
         => #pipelineStepHelper(SymbolsDeclaration, kmodule NAME KSENTENCES endkmodule MODULE | MODULES)
            ...
        </k>
        <koreModule>
          <name>               NAME                                                       </name>
          <sortDeclarations>   SORTS:Declarations                                         </sortDeclarations>
          <symbolDeclarations> DS => DS ++Declarations #declareSymbols(KSENTENCES, SORTS) </symbolDeclarations>
        </koreModule>

   rule #declareSymbols(.KFrontSentences, Set) => .Declarations
   rule #declareSymbols(KS KSS, SORTSSET)
     => #declareSymbolsSentence(KS, SORTSSET) ++Declarations #declareSymbols(KSS, SORTSSET)

   rule #declareSymbolsSentence(ksyntax(ksort(SORT), klabel(SYMBOLNAME), ARGSORTS), SORTSET)
     => symbol SYMBOLNAME { .Names } ( KFrontSorts2KoreSorts(ARGSORTS) ) : SORT { .Sorts } [.Patterns]
        .Declarations
```

```k
  syntax KItem        ::=  "#configurationModulesToTerm"
  syntax Declarations ::=  #toKoreSentences ( Set )     [function]

  rule #processedDefintion( DEF ) ~> #configurationDefinitionToTerm
        =>
       #configurationDefinitionToTerm ~> #processedDefintion ( DEF )

  rule <k> (#configurationDefinitionToTerm => #configurationModulesToTerm ) ... </k>
       <koreDefinition> _ => [ .Patterns ] .Modules </koreDefinition>

  // TODO (Issue): This rule doesn't handle multiple modules. Fix this rule.
  rule <k> #configurationModulesToTerm ... </k>
       <koreDefinition>
          _
            =>
          [ .Patterns ]
             `module`( MODULENAME, SORTDECLS ++Declarations SYMBOLDECLS, [ .Patterns ])
             .Modules
        </koreDefinition>
        <kore>
          ...
          <modules>
            (<koreModule>
                <name>               MODULENAME  </name>
                <sortDeclarations>   SORTDECLS   </sortDeclarations>
                <symbolDeclarations> SYMBOLDECLS </symbolDeclarations>
             </koreModule>
               =>
             .Bag)
            ...
          </modules>
        </kore>

  rule <k> (#configurationModulesToTerm => .K) ... </k>
       <kore>
        ...
        <modules> .Bag </modules>
       </kore>
endmodule
```

```k
module KINK-SYNTAX
  imports KFRONT-SYNTAX
endmodule

module KINK
  imports KFRONT-TO-KORE
endmodule
```

