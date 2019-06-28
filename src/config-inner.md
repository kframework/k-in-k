```k
//require "inner.k"

module CONFIG-CELLS
  imports KCELLS
  imports RULE-LISTS
  syntax CellName ::= r"[a-zA-Z][A-Za-z0-9'_]*"   [token]

  syntax Cell ::= "<" CellName CellProperties ">" K "</" CellName ">" [klabel(configCell)]
  syntax Cell ::= "<" CellName "/>" [klabel(externalCell)]

  syntax CellProperties ::= CellProperty CellProperties [klabel(cellPropertyList)]
                          | ""                          [klabel(cellPropertyListTerminator)]
  syntax CellProperty ::= CellName "=" KString          [klabel(cellProperty)]

endmodule

module CONFIG-INNER // main parsing module for configuration, start symbol: K
  imports K-TERM
  imports CONFIG-CELLS
  imports DEFAULT-LAYOUT
endmodule
```
