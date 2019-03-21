module PEANO
  syntax Pgm ::= Nat
  syntax Layout ::= r"(/\\*([^\\*]|(\\*+([^\\*/])))*\\*+/|//[^\n\r]*|[\\ \n\r\t])*" [klabel(layout)]

  syntax Nat ::= "zero" [klabel(zero)]
               | succ(Nat) [klabel(succ)]
               | plus(Nat, Nat) [function, klabel(plus)]

  rule plus(zero, Y:Nat) => Y
  rule plus(succ(X:Nat), Y:Nat) => succ(plus(X, Y))
endmodule
