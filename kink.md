```k
requires "kore.k"

module KFRONT-COMMON
  imports STRING
  imports KORE-COMMON

  syntax KFrontDeclarations ::= List{KFrontDeclaration, ""}
  syntax KFrontDeclaration  ::= ksyntax(KFrontSort , KFrontLabel, KFrontSorts, KFrontAttributes)
                              | krule(KFrontLabel, KFrontLabel)
  syntax KFrontSort         ::= ksort(Name)
  syntax KFrontSorts        ::= List{KFrontSort, ";"} [klabel(KFrontSorts)]
  syntax KFrontLabel        ::= klabel(Name)
  syntax KFrontAttribute    ::= kattribute(KFrontAttributeName)
  syntax KFrontAttributes   ::= List{KFrontAttribute, ";"} [klabel(KFrontAttributes)]
  syntax KFrontAttributeName ::= "function"

  syntax KFrontModule     ::=  "kmodule" Name KFrontSentences "endkmodule"
  syntax KFrontModules    ::=  List{KFrontModule, " "}                     [klabel(kauxModules)]
  syntax KFrontSentences  ::=  List{KFrontSentence, " "} [klabel(kauxSentences), format(%1%2%n%3)]
  syntax KFrontSentence   ::=  KFrontDeclaration
  syntax KFrontDefinition ::=  KFrontModules
endmodule
```

```k
module KFRONT-TO-KORE
  imports KFRONT-COMMON
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
                  <k> #createModules
                   ~> #withEachSentence(#collectSortDeclarations(.Set))
                   ~> #withEachSentence(#collectSymbols)
                   ~> #toKoreSyntax
                  </k>
                  <kfront> $PGM:KFrontModules </kfront>
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
```

For each empty module in the K Frontend syntax create a new `<koreModule>` cell:

```k
  syntax K ::= "#createModules" | #createModulesAux(KFrontModules)
  rule <k> #createModules => #createModulesAux(MODULES) ... </k>
       <kfront> MODULES </kfront>
  rule <k> #createModulesAux(.KFrontModules) => .K ... </k>
  rule <k> #createModulesAux(kmodule MNAME KS endkmodule MODULES)
        => #createModulesAux(MODULES)
           ...
       </k>
       <modules> .Bag
              => <koreModule>
                   <name> MNAME </name>
                   ...
                 </koreModule>
             ...
       </modules>
```

`#withEachSentence` is a helper function for walking over all `KFrontSentence`s in all modules:

```k
  syntax KFrontSentenceVisitor
  syntax K ::= #withEachSentence(KFrontSentenceVisitor)
             | #withEachSentenceAux(KFrontModules)
             | #visit(KFrontSentenceVisitor, Name, KFrontSentence)
             | #visitNext(KFrontSentenceVisitor)
  rule <k> #withEachSentence(V)
        => #visitNext(V) ~> #withEachSentenceAux(MODULES)
           ...
       </k>
       <kfront> MODULES </kfront>
  rule <k> #visitNext(V) ~> #withEachSentenceAux(kmodule MNAME .KFrontSentences endkmodule MODULES)
        => #visitNext(V) ~> #withEachSentenceAux(MODULES)
           ...
       </k>
  rule <k> #visitNext(V) ~> #withEachSentenceAux(.KFrontModules) => .K ... </k>
  rule <k> #visitNext(V) ~> #withEachSentenceAux(kmodule MNAME (KS KSS) endkmodule MODULES)
        => #visit(V, MNAME, KS) ~> #withEachSentenceAux(kmodule MNAME (KSS) endkmodule MODULES)
           ...
       </k>
  syntax KFrontSentenceVisitor ::= "#nullVisitor"
  rule #visit(#nullVisitor, _, _) => .K
```

Collect sort declarations:

```k
  syntax KFrontSentenceVisitor ::= #collectSortDeclarations(Set)
  rule <k> #visit( #collectSortDeclarations(DECLARED_SORTS), MNAME
                 , ksyntax(ksort(SORT:Name), _, _, _))
        => #visitNext(#collectSortDeclarations(DECLARED_SORTS SetItem(SORT)))
           ...
       </k>
       <koreModule>
         <name> MNAME </name>
         <sortDeclarations>
           DS => DS ++Declarations sort SORT { .Names } [ .Patterns ] .Declarations
         </sortDeclarations>
         ...
       </koreModule>
    requires notBool(SORT in DECLARED_SORTS)
    rule <k> #visit( #collectSortDeclarations(DECLARED_SORTS), _
                   , ksyntax(ksort(SORT:Name), _, _, _))
          => #visitNext(#collectSortDeclarations(DECLARED_SORTS))
             ...
         </k>
      requires SORT in DECLARED_SORTS
    rule <k> #visit( #collectSortDeclarations(DECLARED_SORTS), _, krule(_, _))
          => #visitNext(#collectSortDeclarations(DECLARED_SORTS))
             ...
         </k>
// // TODO: Why doesn't owise work?
//   rule <k> #visit( #collectSortDeclarations(DECLARED_SORTS), _, _)
//         => #visitNext(#collectSortDeclarations(DECLARED_SORTS))
//            ...
//        </k> [owise]
```

Collect symbol declarations

```k
  syntax KFrontSentenceVisitor ::= "#collectSymbols"
  rule <k> #visit(#collectSymbols, MNAME, ksyntax(ksort(SORT:Name), klabel(LABEL), ARGSORTS, _))
        => #visitNext(#collectSymbols)
          ...
      </k>
      <koreModule>
        <name> MNAME </name>
        <symbolDeclarations>
          DS => DS ++Declarations
                symbol LABEL { .Names } ( KFrontSorts2KoreSorts(ARGSORTS) ) : SORT { .Sorts } [.Patterns]
                .Declarations
        </symbolDeclarations>
        ...
      </koreModule>
  rule <k> #visit(#collectSymbols, _, _) => #visitNext(#collectSymbols) ... </k> [owise]
       
// TODO: Take into account sort params. Will need to do a lookup.
   syntax Sorts ::= KFrontSorts2KoreSorts(KFrontSorts) [function]
   rule KFrontSorts2KoreSorts(.KFrontSorts)  => .Sorts
   rule KFrontSorts2KoreSorts(ksort(N) ; SS) => N { .Sorts } , KFrontSorts2KoreSorts(SS)
```

```k
  syntax KItem        ::=  "#toKoreSyntax"
  // TODO (Issue): This rule doesn't handle multiple modules. Fix this rule.
  rule <k> #toKoreSyntax ... </k>
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

  rule <k> #toKoreSyntax => .K ... </k>
       <kore>
         <modules> .Bag </modules>
         ...
       </kore>
```

```k
endmodule
```

```k
module KINK-SYNTAX
  imports KORE-SYNTAX
  imports KFRONT-COMMON
endmodule

module KINK
  imports KFRONT-TO-KORE
endmodule
```

