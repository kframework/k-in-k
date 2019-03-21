module FOOBAR
  syntax Pgm ::= Foo
  syntax Foo ::= "bar" [klabel(bar), function]
               | "buzz" [klabel(buzz)]
  rule bar => buzz
endmodule
