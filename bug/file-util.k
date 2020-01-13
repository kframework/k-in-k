


module FILE-UTIL
  imports K-IO
  imports DOMAINS
  // saveToFile(contents:String, path:String) -> .K
  syntax K ::= saveToFile(String, String) [function]
  syntax K ::= saveToFileHelper(IOInt /* File Descriptor */, K /* to save */) [function]
  rule saveToFile(Contents, Path) => saveToFileHelper(#open(Path, "w"), Contents)
  rule saveToFileHelper(Fd:Int, Contents:String) => saveToFileHelper(Fd, #write(Fd, Contents))
  rule saveToFileHelper(Fd:Int, .K) => #close(Fd)

  // saveToTempFile(contents:String, filenameTemplate:String)
  //            -> tempFilename:IOString
  syntax IOString ::= saveToTempFile(String, String)         [function]
                    | saveToTempFileHelper1(K, IOFile)       [function]
                    | saveToTempFileHelper2(K, String)       [function]
  rule saveToTempFile(CONTENTS, FTEMPLATE)
    => saveToTempFileHelper1(CONTENTS, #mkstemp(FTEMPLATE))
  rule saveToTempFileHelper1(CONTENTS, #tempFile(FILENAME:String, Fd:Int))
    => saveToTempFileHelper2(saveToFileHelper(Fd, CONTENTS), FILENAME:String)
  rule saveToTempFileHelper2(.K, FILENAME)
    => FILENAME

  // readFile(path:String) -> String
  syntax IOString ::= readFile(String) [function]
  syntax IOString ::= readFileHelper(IOInt /* File Descriptor */, K /* reader */, String /* accumulator */) [function]
  rule readFile(S)                           => readFileHelper(#open(S, "r"), .K, "")
  rule readFileHelper(Fd:Int, .K, Acc)       => readFileHelper(Fd, #read(Fd, 4096), Acc)
  rule readFileHelper(Fd:Int, "", Acc)       => readFileHelper(#EBADF, #close(Fd), Acc)
  rule readFileHelper(Fd:Int, S:String, Acc) => readFileHelper(Fd, .K, Acc +String S) [owise]
  rule readFileHelper(#EBADF, .K, Acc)       => Acc
  rule readFileHelper(ERR:IOError, .K, Acc)  => ERR [owise]
endmodule


