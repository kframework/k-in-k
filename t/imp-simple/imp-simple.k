module IMP-SIMPLE
  syntax Layout ::= r"(/\\*([^\\*]|(\\*+([^\\*/])))*\\*+/|//[^\n\r]*|[\\ \n\r\t])*" [klabel(layout)]
  syntax Pgm ::= KCell

  syntax KCell ::= "<k>" KList "</k>" [klabel(kCell)]
  syntax KList ::= KItem "~>" KList   [klabel(kseq)]
                 | ".K"               [klabel(dotk)]
  syntax KItem ::= BExp               [klabel(inj)]

  syntax BExp ::= "True"         [klabel(True)]
                | "False"        [klabel(False)]
                | BExp "&&" BExp [klabel(And)]
  rule <k> True  && B:BExp  => B:BExp </k>
  rule <k> False && B:BExp  => False  </k>
endmodule
