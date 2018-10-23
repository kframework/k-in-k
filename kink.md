```k
requires "ekore.k"
```

```k
module KINK
  imports EKORE

  context (ATTR:Attribute HOLE):Definition
  rule isKResult(_:KoreModule MS:Modules) => isKResult(MS:Modules)

  context (HOLE REST):Modules
  syntax KResult ::= KoreModule

  rule kDefinition(_:KRequireList, MODS:Modules)
    => koreDefinition([ .Patterns ], MODS:Modules)

  rule kModule(MNAME:KModuleName, ATTRS:OptionalAttributes, KIMPORTS:KImportList, DECLS:Declarations)
    => koreModule(MNAME:KModuleName, DECLS:Declarations, [ .Patterns ])

  configuration <k> $PGM:Definition </k>
endmodule
```

