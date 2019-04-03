Parsing utils

```k
module PARSER-UTIL
  imports FILE-UTIL
  imports META

  syntax KItem ::= outerParseFile (String /* file path */) [function, impure]
  syntax KItem ::= outerParseFileHelper(K) [function, impure]
  rule outerParseFile(Path) => outerParseFileHelper(#system("k-light2k5.sh --module FRONTEND-SYNTAX --output kast .build/ekore.k Definition " +String Path))
  rule outerParseFileHelper(#systemResult(0, Stdout, _)) => #parseAST(Stdout)

  syntax KItem ::= outerParse     (String) [function, impure]
  syntax KItem ::= outerParseHelper(K /* contents */, K /* filename */) [function, impure]
  rule outerParse(S) => outerParseHelper(S, #tempFilename("", ""))  // create temp
  rule outerParseHelper(S:String, Path:String) => outerParseHelper(saveToFile(S, Path), Path) // save to temp
  rule outerParseHelper(.K, Path:String) => outerParseHelper(#system("k-light2k5.sh --module FRONTEND-SYNTAX --output kast .build/ekore.k Definition " +String Path), Path) // call system
  rule outerParseHelper(#systemResult(ExitCode, Stdout, Stderr), Path:String) => outerParseHelper(#systemResult(ExitCode, Stdout, Stderr), #remove(Path)) // delete temp
  rule outerParseHelper(#systemResult(0, Stdout, _), .K) => #parseAST(Stdout) // parse ast

  syntax KItem ::= parseWithProds(List /* list of prods */, String /* start symbol */, String /* input */) [function, impure]

endmodule
```
