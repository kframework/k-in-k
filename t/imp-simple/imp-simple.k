module IMP-SIMPLE
  syntax Layout ::= r"(/\\*([^\\*]|(\\*+([^\\*/])))*\\*+/|//[^\n\r]*|[\\ \n\r\t])*" [klabel(layout)]
  syntax Pgm ::= KCell

  syntax KCell ::= "<k>" KList "</k>" [klabel(kCell)]
  syntax KList ::= KItem "~>" KList   [klabel(kseq)]
                 | ".K"               [klabel(dotk)]
  syntax KItem ::= BExp               [klabel(inj)]

  syntax BExpResult ::= "True"        [klabel(True)]
                      | "False"       [klabel(False)]
                      | "#hole"       [klabel(HOLE)]
  syntax BExp ::= BExpResult          [klabel(inj)]
                | "(" BExp ")"        [klabel(Bracket)]
                | BExp "&&" BExp      [klabel(And)]

  rule <k> True  && B:BExp  => B:BExp ... </k>
  rule <k> False && B:BExp  => False ... </k>
  rule <k> B1 && B2 => B1 ~> HOLE && B2 ... </k>
  rule <k> ( B1 ) => B1 ... </k>
endmodule
