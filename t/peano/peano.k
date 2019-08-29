module PEANO-SYNTAX
  syntax Pgm ::= Nat
  syntax Layout ::= r"(/\\*([^\\*]|(\\*+([^\\*/])))*\\*+/|//[^\n\r]*|[\\ \n\r\t])*" [klabel(layout)]

  syntax Nat ::= "zero" [klabel(zero)]
               | succ(Nat) [klabel(succ)]
               | plus(Nat, Nat) [function, klabel(plus)]
endmodule

module PEANO
  imports PEANO-SYNTAX
  rule plus(zero, Y:Nat) => Y
  rule plus(succ(X:Nat), Y:Nat) => succ(plus(X, Y))
endmodule
