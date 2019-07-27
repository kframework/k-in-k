module LANGUAGE-GRAMMAR

syntax Nat ::= Nat "+" Nat     [klabel ( plus  )]
syntax Nat ::= "s" "(" Nat ")" [klabel ( succ  )]
syntax Nat ::= "."             [klabel (zero)]

endmodule
