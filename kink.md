```k
requires "ekore.k"
```

```k
module KINK
  imports EKORE

  configuration <k> $PGM:Definition </k>

  rule kDefinition(_:KRequireList, MODS:Modules)
    => koreDefinition([ .Patterns ], MODS:Modules)
  rule kModule(MNAME:KModuleName, ATTRS:OptionalAttributes, KIMPORTS:KImportList, DECLS:Declarations)
    => koreModule(MNAME:KModuleName, DECLS:Declarations, [ .Patterns ])
       [anywhere]

endmodule
```

