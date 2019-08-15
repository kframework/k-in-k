module EXPRESSIONS
  syntax Layout ::= r"(/\\*([^\\*]|(\\*+([^\\*/])))*\\*+/|//[^\n\r]*|[\\ \n\r\t])*" [klabel(layout)]
  syntax Pgm ::= ImpCell
 
  syntax K ::= KItem "~>" K                             [klabel(kseq)]
                 | ".K"                                 [klabel(dotk)]
  syntax KItem ::= BExp                                 [klabel(inj)]

  configuration <imp>
                  <k> $PGM:K </k>
                  <a> False:BExpResult </a>
                </imp>

  syntax ImpCell ::= "<imp>" KCell ACell "</imp>"       [klabel(impCell)]
  syntax KCell ::= "<k>" K "</k>"                       [klabel(kCell)]
  syntax ACell ::= "<a>" BExpResult "</a>"              [klabel(aCell)]

  syntax BExpResult ::= "True"                          [klabel(True)]
                      | "False"                         [klabel(False)]
                      | "#hole"                         [klabel(HOLE)]
  syntax BExp ::= BExpResult                            [klabel(inj)]
                | "(" BExp ")"                          [klabel(Bracket)]
                | BExp "&&" BExp                        [klabel(And)]

  syntax Statement ::= "a" ":=" BExp                    [klabel(assignToA)]

//  rule <k> True  && B:BExp  => B:BExp ... </k>
//  rule <k> False && B:BExp  => False ... </k>
//  rule <k> B1 && B2 => B1 ~> #hole && B2 ... </k>
//  rule <k> ( B1 ) => B1 ... </k>
//
//  rule <imp>
//         <k> a := B:BExpResult  ~> REST </k>
//         <a> _:BExpResult </a>
//       </imp>
//    => <imp>
//         <k> REST </k>
//         <a> B:BExpResult </a>
//       </imp>
endmodule
