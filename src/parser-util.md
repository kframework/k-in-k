Parsing utils

```k
module PARSER-UTIL
  imports FILE-UTIL
  imports META

  syntax KItem ::= parseFileOuter (String /* file path */) [function, impure]
  syntax KItem ::= parseFileHelper(K) [function, impure]
  rule parseFileOuter(Path) => parseFileHelper(#system("k-light2k5.sh --module OUTER-SYNTAX --output kast .build/ekore.k Definition " +String Path))
  rule parseFileHelper(#systemResult(0, Stdout, _)) => #parseAST(Stdout)

  syntax KItem ::= parseOuter     (String) [function, impure]
  rule parseOuter(S)
    => parseHelper(S, #tempFilename("", ""), "k-light2k5.sh --module OUTER-SYNTAX --output kast .build/ekore.k Definition ")  // create temp

  syntax KItem ::= parseEKore     (String) [function, impure]
  rule parseEKore(S)
    => parseHelper(S, #tempFilename("", ""), "k-light2k5.sh --module EKORE-SYNTAX --output kast .build/ekore.k Definition ")

  syntax KItem ::= parseHelper(
                        K /* contents */,
                        K /* filename */,
                        String /* cmd to call */) [function, impure]
  rule parseHelper(S:String, Path:String, Cmd)
    => parseHelper(saveToFile(S, Path), Path, Cmd) // save to temp
  rule parseHelper(.K, Path:String, Cmd)
    => parseHelper(#system(Cmd +String Path), Path, Cmd) // call system
  rule parseHelper(#systemResult(ExitCode, Stdout, Stderr), Path:String, Cmd)
    => parseHelper(#systemResult(ExitCode, Stdout, Stderr), #remove(Path), Cmd) // delete temp
  rule parseHelper(#systemResult(0, Stdout, _), .K, _)
    => #parseAST(Stdout) // parse ast

  syntax KItem ::= parseWithProds(List /* list of prods */, String /* start symbol */, String /* input */) [function, impure]

endmodule
```
