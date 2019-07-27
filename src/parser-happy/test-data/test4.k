module LANGUAGE-GRAMMAR

syntax Nat ::= Nat "+" Nat     [klabel ( plus  )]
syntax Nat ::= "s" "(" Nat ")" [klabel ( succ  )]
syntax Nat ::= "."             [klabel (zero)]

syntax Foo ::= Foo "+" Foo     [klabel ( fooplus  )]
syntax Foo ::= "s" "(" Foo ")" [klabel ( foosucc  )]
syntax Foo ::= "."             [klabel (foozero)]

endmodule
