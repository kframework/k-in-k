module FOOBAR-SYNTAX
  syntax Layout ::= r"(/\\*([^\\*]|(\\*+([^\\*/])))*\\*+/|//[^\n\r]*|[\\ \n\r\t])*" [klabel(layout)]

  syntax Pgm ::= Foo
  syntax Foo ::= "bar" [klabel(bar), function]
               | "buzz" [klabel(buzz)]
endmodule

module FOOBAR
  imports FOOBAR-SYNTAX
  rule bar => buzz
endmodule
