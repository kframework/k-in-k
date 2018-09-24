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

  syntax Name ::= "inj" | "From" | "To" | "function"

  configuration <T>
                  <k> #createModules
                   ~> #withEachSentence(#collectSortDeclarations(.Set))
                   ~> #withEachSentence(#collectSymbols)
                   ~> #withEachSentence(#translateFunctionRules)
                   ~> #toKoreSyntax
                  </k>
                  <kfront> $PGM:KFrontModules </kfront>
                  <koreDefinition> .K </koreDefinition>
                  <kore>
                    <definitionAttributes> [ .Patterns ] </definitionAttributes>
                    <modules>
                      <koreModule multiplicity="*" type="List">
                        <name> .K </name>
                        <sorts>
                          <sortDeclaration multiplicity="*" type="List" > .K </sortDeclaration>
                        </sorts>
                        <koreSymbols>
                          <koreSymbol multiplicity="*" type="Set">
                              <symbolDeclaration> .K:Declaration </symbolDeclaration>
                          </koreSymbol>
                        </koreSymbols>
                        <axioms>
                          <axiomDeclaration multiplicity="*" type="List"> .K:Declaration </axiomDeclaration>
                        </axioms>
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
                   <koreSymbols>
                     <koreSymbol>
                       <symbolDeclaration>
                           (symbol inj { From , To , .Names } ( From , .Sorts) : To [ .Patterns ])
                       </symbolDeclaration>
                       ...
                     </koreSymbol>
                   </koreSymbols>
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
         <sorts> SS
              => (SS <sortDeclaration> sort SORT { .Names } [ .Patterns ] </sortDeclaration>)
         </sorts>
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
  rule <k> #visit(#collectSymbols, MNAME, ksyntax(ksort(SORT:Name), klabel(LABEL), ARGSORTS, FATTRS))
        => #visitNext(#collectSymbols)
          ...
       </k>
       <koreModule>
         <name> MNAME </name>
         <koreSymbols> .Bag =>
           <koreSymbol>
             <symbolDeclaration>
               symbol LABEL { .Names } ( KFrontSorts2KoreSorts(ARGSORTS) ) : SORT { .Sorts } [ KFrontAttributes2KoreAttributes(FATTRS) ]
             </symbolDeclaration>
           </koreSymbol>
           ...
         </koreSymbols>
         ...
       </koreModule>
  rule <k> #visit(#collectSymbols, _, krule(_, _)) => #visitNext(#collectSymbols) ... </k>
//  //TODO: Owise rule fails here as well.
//  rule <k> #visit(#collectSymbols, _, _) => #visitNext(#collectSymbols) ... </k>

  syntax Patterns ::= KFrontAttributes2KoreAttributes(KFrontAttributes) [function]
  rule KFrontAttributes2KoreAttributes(.KFrontAttributes) => .Patterns
  rule KFrontAttributes2KoreAttributes(kattribute(function) ; S)
    => function { .Sorts } (.Patterns)
     , KFrontAttributes2KoreAttributes(S)

// TODO: Take into account sort params. Will need to do a lookup.
   syntax Sorts ::= KFrontSorts2KoreSorts(KFrontSorts) [function]
   rule KFrontSorts2KoreSorts(.KFrontSorts)  => .Sorts
   rule KFrontSorts2KoreSorts(ksort(N) ; SS) => N { .Sorts } , KFrontSorts2KoreSorts(SS)
```

Translate rewrites for functional symbols:

```k
  syntax KFrontSentenceVisitor ::= "#translateFunctionRules"
  syntax Name ::= "R"
  rule <k> #visit(#translateFunctionRules, MNAME, krule(klabel(LHS), klabel(RHS)))
        => #visitNext(#translateFunctionRules)
           ...
       </k>
       <koreModule>
         <name> MNAME </name>
           <koreSymbol>
             <symbolDeclaration>
               symbol LHS:Name { _ } ( _ ) : SORTNAME { .Sorts } [ ATTRS ]
             </symbolDeclaration>
             ...
           </koreSymbol>
         <axioms> .Bag =>
           <axiomDeclaration>
             axiom{ R , .Names}
                \equals{ SORTNAME { .Sorts }, R }
                       ( LHS { .Sorts } ( .Patterns )
                       , RHS { .Sorts } ( .Patterns )
                       )
                [ .Patterns ]
           </axiomDeclaration>
         </axioms>
         ...
       </koreModule>
    requires (function { .Sorts } (.Patterns)) inPatterns ATTRS

  rule <k> #visit(#translateFunctionRules, MNAME, krule(klabel(LHS), klabel(RHS)))
        => #visitNext(#translateFunctionRules)
           ...
       </k>
       <koreModule>
         <name> MNAME </name>
         <koreSymbol>
           <symbolDeclaration>
             symbol LHS { _ } ( _ ) : SORTNAME { .Sorts } [ ATTRS ]
           </symbolDeclaration>
         </koreSymbol>
         ...
       </koreModule>
    requires notBool((function { .Sorts } (.Patterns)) inPatterns ATTRS)

  rule <k> #visit(#translateFunctionRules, MNAME, ksyntax(_, _, _, _))
        => #visitNext(#translateFunctionRules)
           ...
       </k>
```

Finally, convert each `<module>` cell into actual kore syntax.
TODO: We don't handle multiple modules.

```k
  syntax KItem ::= "#toKoreSyntax"
                 | "#writeSortDeclarations"
                 | "#writeSymbolDeclarations"
                 | "#writeAxioms"
  rule <k> #toKoreSyntax
        => #writeSortDeclarations ~> #writeSymbolDeclarations ~> #writeAxioms ~> #toKoreSyntax
       </k>
       <koreDefinition>
        .K => [ .Patterns ]
              `module`( MNAME , .Declarations , [.Patterns])
       </koreDefinition>
       <kore>
         <modules>
           <koreModule>
           <name> MNAME </name>
           ...
           </koreModule>
         </modules>
         ...
       </kore>
```

```k
  rule <k> #writeSortDeclarations ... </k>
       <koreDefinition>
           [ ATTRS ] `module`( MNAME , DECS , [.Patterns])
        => [ ATTRS ] `module`( MNAME , DECS ++Declarations SORTDECL, [.Patterns])
       </koreDefinition>
       <name> MNAME </name>
       <sorts>
         <sortDeclaration> SORTDECL:Declaration </sortDeclaration> => .Bag
         ...
       </sorts>

  rule <k> #writeSortDeclarations => .K ... </k>
       <sorts> .Bag </sorts>
```

```k
  rule <k> #writeSymbolDeclarations ... </k>
       <koreDefinition>
           [ ATTRS ] `module`( MNAME , DECS , [.Patterns])
        => [ ATTRS ] `module`( MNAME , DECS ++Declarations SYMBOLDECL, [.Patterns])
       </koreDefinition>
       <name> MNAME </name>
       <koreSymbols>
         <koreSymbol>
           <symbolDeclaration>
             SYMBOLDECL:Declaration
           </symbolDeclaration>
           ...
         </koreSymbol> => .Bag
         ...
       </koreSymbols>

  rule <k> #writeSymbolDeclarations => .K ... </k>
       <koreSymbols> .Bag </koreSymbols>
```

```k
  rule <k> #writeAxioms ... </k>
       <koreDefinition>
           [ ATTRS ] `module`( MNAME , DECS , [.Patterns])
        => [ ATTRS ] `module`( MNAME , DECS ++Declarations AXIOM, [.Patterns])
       </koreDefinition>
       <name> MNAME </name>
       <axioms>
         <axiomDeclaration>
           AXIOM:Declaration
         </axiomDeclaration> => .Bag
         ...
       </axioms>

  rule <k> #writeAxioms => .K ... </k>
       <axioms> .Bag </axioms>
```

```k
  rule <k> #toKoreSyntax ... </k>
       <modules>
         (<koreModule>
             <sorts> .Bag </sorts>
             <koreSymbols> .Bag </koreSymbols>
             <axioms> .Bag </axioms>
             ...
          </koreModule>
            =>
          .Bag)
       </modules>

  rule <k> #toKoreSyntax => .K ... </k>
       <modules> .Bag </modules>
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

