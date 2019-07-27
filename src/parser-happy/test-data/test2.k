module LANGUAGE-GRAMMAR

syntax Nat ::= "plus" "(" Nat "," Nat ")" [ klabel ( plus  )]
syntax Nat ::= "succ" "(" Nat ")"         [ klabel ( succ  )]
syntax Nat ::= "zero"                     [klabel (zero)]

endmodule
