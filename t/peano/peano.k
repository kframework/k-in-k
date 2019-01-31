module PEANO
  syntax Nat ::= "zero"
               | succ(Nat)
               | plus(Nat, Nat) [function]

  rule plus(zero, Y:Nat) => Y

  rule plus(succ(X:Nat), Y:Nat) => succ(plus(X, Y))

endmodule
