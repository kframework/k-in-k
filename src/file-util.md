Helper methods for saving and loading contents from a file

```k
module FILE-UTIL
  imports K-IO
  imports DOMAINS
  // saveToFile(contents:String, path:String) -> .K
  syntax K ::= saveToFile(String, String) [function, impure]
  syntax K ::= saveToFileHelper(IOInt /* File Descriptor */, K /* to save */) [function, impure]
  rule saveToFile(Contents, Path) => saveToFileHelper(#open(Path, "w"), Contents)
  rule saveToFileHelper(Fd:Int, Contents:String) => saveToFileHelper(Fd, #write(Fd, Contents))
  rule saveToFileHelper(Fd:Int, .K) => #close(Fd)

  // saveToTempFile(contents:String, filenamePrefix:String, filenameSuffix:String)
  //            -> tempFilename:IOString
  syntax IOString ::= saveToTempFile(String, String, String) [function, impure]
                    | saveToTempFileHelper1(K, IOString)     [function, impure]
                    | saveToTempFileHelper2(K, String)       [function, impure]
  rule saveToTempFile(CONTENTS, FPREFIX, FSUFFIX)
    => saveToTempFileHelper1(CONTENTS, #tempFilename(FPREFIX, FSUFFIX))
  rule saveToTempFileHelper1(CONTENTS, FILENAME:String)
    => saveToTempFileHelper2(saveToFile(CONTENTS, FILENAME), FILENAME:String)
  rule saveToTempFileHelper2(.K, FILENAME)
    => FILENAME

  // readFile(path:String) -> String
  syntax IOString ::= readFile(String) [function, impure]
  syntax IOString ::= readFileHelper(IOInt /* File Descriptor */, K /* reader */, String /* accumulator */) [function, impure]
  rule readFile(S) => readFileHelper(#open(S, "r"), .K, "")
  rule readFileHelper(Fd:Int,   .K, Acc) => readFileHelper(Fd, #read(Fd, 4096), Acc)
  rule readFileHelper(Fd:Int,    S, Acc) => readFileHelper(Fd, .K, Acc +String S)
  rule readFileHelper(Fd:Int, #EOF, Acc) => readFileHelper(#EBADF, #close(Fd), Acc)
  rule readFileHelper(#EBADF, .K, Acc) => Acc

endmodule
```
