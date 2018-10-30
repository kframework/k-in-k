```k
requires "ekore.k"
```

```k
module KINK-CONFIGURATION
  imports EKORE-ABSTRACT

  configuration <k> $PGM:Definition </k>
endmodule
```

```k
module K-MODULE-TO-KORE-MODULE
  imports KINK-CONFIGURATION

  rule kDefinition(_:KRequireList, MODS:Modules)
    => koreDefinition([ .Patterns ], MODS:Modules)
  rule kModule(MNAME:KModuleName, ATTRS:OptionalAttributes, KIMPORTS:KImportList, DECLS:Declarations)
    => koreModule(MNAME:KModuleName, DECLS:Declarations, [ .Patterns ])
       [anywhere]
endmodule
```

```k
module KINK
  imports K-MODULE-TO-KORE-MODULE
endmodule
```

