```k
module COMMAND-LINE-SYNTAX
  imports STRING-SYNTAX
  syntax KItem ::= "#parseCommandLine" "(" CommandLine "," Pgm ")"
  syntax Pgm
  syntax CommandLine ::= "kompile"
                       | "kast" String
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
        => PGM ~> #kastPipeline(PATH)
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

  syntax K ::= "#ekorePipeline" [function]
  rule #ekorePipeline
    => #parseToEKore
    ~> #defnToConfig
    ~> #flattenProductions
    ~> #productionsToSortDeclarations
    ~> #productionsToSymbolDeclarations
    ~> #translateFunctionRules
```

```k
endmodule
```
