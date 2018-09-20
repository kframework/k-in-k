```k
requires "kore.k"

module KFRONT-SYNTAX
  imports STRING
  imports KORE-SYNTAX

  syntax KFrontDeclarations ::= List{KFrontDeclaration, ""}
  syntax KFrontDeclaration  ::= ksyntax(KFrontSort , KFrontLabel)
  syntax KFrontSort         ::= ksort(Name)
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
  imports DOMAINS

  syntax Processed   ::=  #processedDefintion ( KFrontDefinition )

  syntax Intermdiate ::=   #initialization    ( KFrontDefinition )
                         | #sortDeclaration   ( Intermdiate )   [strict]
                         | #symbolDeclaration ( Intermdiate )   [strict]
                         |  Processed

  syntax KResult    ::= Processed
  syntax KItem      ::=  "#done"
                       | "#configurationDefinitionToTerm"

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
                        <name>               .K   </name>
                        <sortDeclarations>   .Set </sortDeclarations>
                        <symbolDeclarations> .Set </symbolDeclarations>
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



   syntax Set ::=   #declareSorts         ( KFrontSentences )     [function]
                  | #declareSortsSentence ( KFrontSentence  )     [function]

   rule #sortDeclaration( #processedDefintion( DEF ) ) => #pipelineStepHelper( SortsDeclaration, .KFrontModules | DEF )


   rule <k>
            (#pipelineStepHelper( SortsDeclaration, MODULE | kmodule NAME KSENTENCES endkmodule MODULES)
              =>
             #pipelineStepHelper( SortsDeclaration, kmodule NAME KSENTENCES endkmodule MODULE | MODULES))
           ...
       </k>
       <koreModule>
         <name>              NAME                              </name>
         <sortDeclarations> .Set => #declareSorts( KSENTENCES ) </sortDeclarations>
         ...
       </koreModule>

   rule #declareSorts( .KFrontSentences ) => .Set
   rule #declareSorts( KSNTNC KSNTNCS ) => #declareSortsSentence( KSNTNC ) #declareSorts( KSNTNCS )

   rule #declareSortsSentence( ksyntax( ksort ( SORTNAME:Name ), _ )) => SetItem( sort SORTNAME { .Names } [ .Patterns ])
   rule #declareSortsSentence( KS ) => .Set    [owise]

   syntax Set ::=  #declareSymbols         ( KFrontSentences , Set ) [function]
                 | #declareSymbolsSentence ( KFrontSentence , Set )  [function]

   rule #symbolDeclaration( #processedDefintion ( DEF )) => #pipelineStepHelper( SymbolsDeclaration, .KFrontModules | DEF )


   rule <k> (#pipelineStepHelper( SymbolsDeclaration, MODULE | kmodule NAME KSENTENCES endkmodule MODULES)
              =>
            #pipelineStepHelper( SymbolsDeclaration, kmodule NAME KSENTENCES endkmodule MODULE | MODULES))
           ...
       </k>
       <koreModule>
         <name>               NAME                                          </name>
         <sortDeclarations>   SORTSSET                                      </sortDeclarations>
         <symbolDeclarations> .Set => #declareSymbols(KSENTENCES, SORTSSET) </symbolDeclarations>
       </koreModule>

   rule #declareSymbols( .KFrontSentences, Set ) => .Set

   rule #declareSymbols( KSNTNC KSNTNCS, SORTSSET)
               =>
        #declareSymbolsSentence( KSNTNC, SORTSSET) #declareSymbols( KSNTNCS, SORTSSET )

   rule #declareSymbolsSentence( ksyntax( ksort( SRTNAME ) , klabel( SYMBOLNAME )) , SORTSET)
          =>
        SetItem(symbol SYMBOLNAME { .Names } ( .Sorts ) : SRTNAME [.Patterns])
           requires (sort SRTNAME { .Names } [ .Patterns] in SORTSET)

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
             `module`( MODULENAME, #toKoreSentences( SYMBOLDECLS SORTDECLS ), [ .Patterns ])
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

  rule #toKoreSentences( .Set )                 => .Declarations
  rule #toKoreSentences( SetItem (DECL) DECLS ) => DECL #toKoreSentences( DECLS )

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
