```k
module COMMAND-LINE-SYNTAX
  imports STRING-SYNTAX
  syntax KItem ::= "#parseCommandLine" "(" CommandLine "," Pgm ")"
  syntax Pgm

  syntax Path ::= r"[\\\\./a-zA-Z0-9_-][\\\\./a-zA-Z0-9_-]*" [token]
  syntax String ::= token2String(KItem) [function, functional, hook(STRING.token2string)]
  syntax CommandLine ::= "kompile"
                       | "kast" Path
                       | "ekore-to-kore"
endmodule
```

```k
module COMMAND-LINE
  imports COMMAND-LINE-SYNTAX

  imports PARSE-OUTER
  imports PARSE-PROGRAM
  imports PARSE-TO-EKORE

  imports FRONTEND-MODULES-TO-KORE-MODULES
  imports FLATTEN-PRODUCTIONS
  imports OUTER-ABSTRACT
  imports NON-FUNCTIONAL-PRODUCTIONS-TO-CONSTRUCTORS
  imports PRODUCTIONS-TO-SORT-DECLARATIONS
  imports PRODUCTIONS-TO-SYMBOL-DECLARATIONS
  imports TRANSLATE-FUNCTION-RULES
  imports REMOVE-FRONTEND-DECLARATIONS
```

Command line options
====================

`kompile` K/Kore definition specified in the `$PGM` variable.

```k
  rule <k> #parseCommandLine(kompile, PGM)
        => PGM ~> #ekorePipeline ~> #filterKoreDeclarations
           ...
       </k>
```

`kast PATH`: Generate a concrete grammar for parsing programs using the K/Kore
definition specified in the `$PGM` variable, and use it to parse the program at
the `PATH`:

```k
  rule <k> #parseCommandLine(kast PATH, PGM)
        => PGM ~> #kastPipeline(token2String(PATH))
           ...
       </k>
```

`ekore-to-kore`: Convert the EKore definition specified in `$PGM`
to kore syntax. Frontend declarations that are not captured completely by
the kore definition are kept.

```k
  rule <k> #parseCommandLine(ekore-to-kore, PGM)
        => PGM ~> #ekorePipeline
           ...
       </k>
```

```k
  syntax KItem ::= "#success"
  rule <k> P:Pattern ~> (#success => .K) ... </k>
       <exit-code> _ => 0 </exit-code>
  rule <k> #success => .K ... </k>
       <exit-code> _ => 0 </exit-code>
```

High-level pipeline steps
=========================

```k
  syntax K ::= "#kastPipeline" "(" String ")" [function]
  rule #kastPipeline(PATH)
    => #parseOuter
    ~> #defnToConfig
    ~> #flattenProductions
    ~> #collectGrammar
    ~> #parseProgramPath(PATH)
    ~> #success

  syntax K ::= "#ekorePipeline" [function]
  rule #ekorePipeline
    => #parseToEKore
    ~> #defnToConfig
    ~> #flattenProductions
    ~> #nonFunctionProductionsToConstructors
    ~> #productionsToSortDeclarations
    ~> #productionsToSymbolDeclarations
    ~> #translateRules
    ~> #success
```

```k
endmodule
```
