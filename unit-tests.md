```k
module UNIT-TESTS-SPEC
    imports KINK
```

`#frontendModulesToKoreModules`
-------------------------------

Definitions with both K and Kore modules are allowed:

```k
    rule <pipeline> #frontendModulesToKoreModules => .K </pipeline>
         <k> kDefinition( .KRequireList
                        , kModule( #token("Foo", "UpperName")
                                 , noAtt
                                 , .KImportList
                                 , .Declarations
                                 )
                          koreModule( #token("Bar", "UpperName")
                                    , .Declarations
                                    , [ .Patterns ]
                                    )
                          .Modules
                        )
          => [ .Patterns ]
             koreModule( #token("Foo", "UpperName")
                       , .Declarations
                       , [ .Patterns ]
                       )
             koreModule( #token("Bar", "UpperName")
                       , .Declarations
                       , [ .Patterns ]
                       )
         </k>
```

```k
endmodule
```
