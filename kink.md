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
                      <koreModule multiplicity="*" type="List">
                        <name> .K </name>
                        <sorts>
                          <sortDeclaration multiplicity="*" type="List" > .K </sortDeclaration>
                        </sorts>
                        <symbols>
                          <xsymbol multiplicity="*" type="List">
                              <symbolName> .K:Name </symbolName>
                              <symbolDeclaration> .K:Declaration </symbolDeclaration>
                          </xsymbol>
                        </symbols>
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
                   <symbols>
                     <xsymbol>
                       <symbolName> inj </symbolName>
                       <symbolDeclaration>
                           (symbol inj { From , To , .Names } ( From , .Sorts) : To [ .Patterns ])
                           </symbolDeclaration>
                     </xsymbol>
                   </symbols>
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
  rule <k> #visit(#collectSymbols, MNAME, ksyntax(ksort(SORT:Name), klabel(LABEL), ARGSORTS, _))
        => #visitNext(#collectSymbols)
          ...
       </k>
       <koreModule>
         <name> MNAME </name>
         <symbols> .Bag =>
           <xsymbol>
             <symbolName> LABEL </symbolName>
             <symbolDeclaration>
               symbol LABEL { .Names } ( KFrontSorts2KoreSorts(ARGSORTS) ) : SORT { .Sorts } [.Patterns]
             </symbolDeclaration>
           </xsymbol>
           ...
         </symbols>
         ...
       </koreModule>
  rule <k> #visit(#collectSymbols, _, krule(_, _)) => #visitNext(#collectSymbols) ... </k>
//  //TODO: Owise rule fails here as well.
//  rule <k> #visit(#collectSymbols, _, _) => #visitNext(#collectSymbols) ... </k>

// TODO: Take into account sort params. Will need to do a lookup.
   syntax Sorts ::= KFrontSorts2KoreSorts(KFrontSorts) [function]
   rule KFrontSorts2KoreSorts(.KFrontSorts)  => .Sorts
   rule KFrontSorts2KoreSorts(ksort(N) ; SS) => N { .Sorts } , KFrontSorts2KoreSorts(SS)
```

Finally, convert each `<module>` cell into actual kore syntax.
TODO: We don't handle multiple modules.

```k
  syntax KItem ::= "#toKoreSyntax"
                 | "#writeSortDeclarations"
                 | "#writeSymbolDeclarations"
  rule <k> #toKoreSyntax
        => #writeSortDeclarations ~> #writeSymbolDeclarations ~> #toKoreSyntax
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
       <symbols>
         <xsymbol>
           <symbolDeclaration>
             SYMBOLDECL:Declaration
           </symbolDeclaration>
           ...
         </xsymbol> => .Bag
         ...
       </symbols>

  rule <k> #writeSymbolDeclarations => .K ... </k>
       <symbols> .Bag </symbols>
```

```k
  rule <k> #toKoreSyntax ... </k>
       <modules>
         (<koreModule>
             <sorts> .Bag </sorts>
             <symbols> .Bag </symbols>
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

