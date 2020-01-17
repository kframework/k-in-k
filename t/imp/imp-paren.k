// Copyright (c) 2014-2018 K Team. All Rights Reserved.

module DOMAINS-SYNTAX
  syntax Map ::= ".Map" [klabel(emptyMap)]
               | K "|->" K [klabel(mapItem)]
               | Map Map [klabel(mapConcat), left]
  syntax Set ::= "keys" "(" Map ")" [klabel(keysOfMap)]

  syntax Int ::= r"[0-9]+" [prefer, token]
               | Int "<=Int" Int [klabel(lteInt)]
               | Int "+Int" Int [klabel(plusInt)]
               | Int "-Int" Int [klabel(minusInt)]
               | Int "/Int" Int [klabel(divInt)]
               | Int "=/=Int" Int [klabel(neInt)]
  syntax Id //::= r"(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_]*"     [token, autoReject]
  syntax Bool ::= "true"  [token] 
                | "false" [token]
                | "notBool" Bool [klabel(notBool)]
                | K "in" Set [klabel(keyInSet)]

  syntax Layout ::= r"(/\\*([^\\*]|(\\*+([^\\*/])))*\\*+/|//[^\n\r]*|[\\ \n\r\t])*"
endmodule

module IMP-PAREN-SYNTAX
  imports DOMAINS-SYNTAX

  syntax AExp  ::= Int | Id
                 | "-" Int                    [klabel(uminus)]
                 | AExp "/" AExp              [klabel(div), left, strict]
                 > AExp "+" AExp              [klabel(plus), left, strict]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [klabel(lte), seqstrict]
                 | "!" BExp                   [klabel(not), strict]
                 > BExp "&&" BExp             [klabel(and), left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"                    [klabel(emptyBlock)]
                 | "{" Stmt "}"               [klabel(block)]
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [klabel(asgn), strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [klabel(if), strict(1)]
                 | "while" "(" BExp ")" Block [klabel(while)]
                 > Stmt Stmt                  [klabel(stmts), left]
  syntax Pgm ::= "int" Ids ";" Stmt           [klabel(start)]
  syntax Ids ::= Id // List{Id,","}
               | Id "," Ids  [klabel(consIds)]
               // | ""      [klabel(emptyIds)]
               | ".Ids"     [klabel(emptyIds)]
endmodule


module IMP-PAREN
  imports IMP-PAREN-SYNTAX
  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .Map </state>
                </T>

// AExp
  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>
  rule (I1 / I2) => (I1 /Int I2)  requires I2 =/=Int 0
  rule (I1 + I2) => (I1 +Int I2)
  rule (- I1) => (0 -Int I1)
// BExp
  rule (I1 <= I2) => (I1 <=Int I2)
  rule (! T) => notBool T
  rule (true && B) => B
  rule (false && _) => false
// Block
  rule {} => .K   [structural]
  rule {S} => S  [structural]
// Stmt
  rule <k> X = I:Int; => .K ...</k> <state>... X |-> (_ => I) ...</state>
  rule (S1:Stmt (S2:Stmt)) => (S1 ~> S2)  [structural]
  rule (if (true)  S else _) => S
  rule (if (false) _ else S) => S
  rule (while (B) S) => if (B) {S while (B) S} else {}  [structural]
// Pgm
  rule <k> int ((X,Xs) => Xs);_ </k> <state> Rho:Map (.Map => (X|->0)) </state>
    requires notBool (X in keys(Rho))
  rule (int .Ids; S) => S  [structural]

// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]
endmodule

