module FOOBAR
  syntax Layout ::= r"(/\\*([^\\*]|(\\*+([^\\*/])))*\\*+/|//[^\n\r]*|[\\ \n\r\t])*" [klabel(layout)]

  syntax Pgm ::= Foo
  syntax Foo ::= "bar" [klabel(bar), function]
               | "buzz" [klabel(buzz)]
  configuration <T> <k> $PGM </k> <env> .K </env> </T>
endmodule
