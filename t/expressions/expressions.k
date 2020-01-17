module EXPRESSIONS
  syntax Layout ::= r"(/\\*([^\\*]|(\\*+([^\\*/])))*\\*+/|//[^\n\r]*|[\\ \n\r\t])*" [klabel(layout)]
  syntax Pgm ::= ExpCell
 
  syntax K ::= KItem "~>" K                             [klabel(kseq)]
                 | ".K"                                 [klabel(dotk)]
  syntax KItem ::= BExp                                 [klabel(inj)]

  configuration <exp>
                  <k> $PGM:K </k>
                </exp>

  syntax ExpCell ::= "<exp>" KCell "</exp>"             [klabel(expCell)]
  syntax KCell ::= "<k>" K "</k>"                       [klabel(kCell)]

  syntax BExpResult ::= "True"                          [klabel(True)]
                      | "False"                         [klabel(False)]
  syntax BExp ::= BExpResult                            [klabel(inj)]
                | "(" BExp ")"                          [klabel(Bracket)]
                | BExp "&&" BExp                        [klabel(And)]

//  rule <k> True  && B:BExp  => B:BExp ... </k>
//  rule <k> False && B:BExp  => False ... </k>
//  rule <k> B1 && B2 => B1 ~> #hole && B2 ... </k>
//  rule <k> ( B1 ) => B1 ... </k>
//
//  rule <exp>
//         <k> B:BExpResult  ~> REST </k>
//       </exp>
//    => <exp>
//         <k> REST </k>
//       </exp>

//      context HOLE:BExp && B:BExp
//  =>  context <exp> <k> HOLE:BExp && B:BExp ... </k> </exp>
//  =>  context <exp> <k> HOLE:BExp && B:BExp ... </k> </exp>
//  =>  context <exp> <k> (HOLE:BExp => HOLE:BExp) && B:BExp ... </k> </exp>
//  =>  context <exp> <k> (HOLE:BExp => HOLE:BExp) && B:BExp ... </k> </exp>
//  =>  context <exp> <k> (HOLE:BExp => HOLE:BExp) && B:BExp ... </k> </exp>
//  =>  context cooled = <exp> <k> HOLE:BExp && B:BExp ... </k> </exp>
                frozen = FREEZER1&& B:BExp
                heated = <exp> <k> HOLE:BExp ~> FREEZER1&& B:BExp ... </k> </exp>
//              =>  <exp> <k> HOLE:BExp && B:BExp ... </k> </exp>
endmodule
