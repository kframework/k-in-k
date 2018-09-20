Hello World!

```k
module KINK-SYNTAX
  imports STRING

  syntax KFrontDeclarations ::= List{KFrontDeclaration, ""}
  syntax KFrontDeclaration  ::= ksyntax(KFrontSort, KFrontLabel) 
  syntax KFrontSort         ::= ksort(String)
  syntax KFrontLabel        ::= klabel(String)
endmodule
```

```k
module KINK
  imports KINK-SYNTAX
  
  configuration <kink> $PGM:KFrontDeclarations </kink>
endmodule
```
