
require "file-util.k"
require "parser-gen.k"

module COMMAND-LINE-SYNTAX
  imports STRING-SYNTAX
  syntax KItem ::= "#parseCommandLine" "(" CommandLine "," Pgm ")"
  syntax Pgm

  syntax Path ::= r"[\\\\./a-zA-Z0-9_-][\\\\./a-zA-Z0-9_-]*" [token]
  syntax String ::= token2String(Path) [function, functional, hook(STRING.token2string)]
  syntax CommandLine ::= "kompile"
                       | "kast" Path
                       | "frontend-to-ekore"
                       | "ekore-to-kore"
endmodule



module COMMAND-LINE
  imports COMMAND-LINE-SYNTAX

  imports PARSE-OUTER
  imports PARSE-PROGRAM
  imports PARSE-CONFIG
  imports PARSE-RULE
  imports PARSE-TO-EKORE

  imports FRONTEND-MODULES-TO-KORE-MODULES
  imports FLATTEN-PRODUCTIONS
  imports OUTER-ABSTRACT
  imports NON-FUNCTIONAL-PRODUCTIONS-TO-CONSTRUCTORS
  imports PRODUCTIONS-TO-SORT-DECLARATIONS
  imports PRODUCTIONS-TO-SYMBOL-DECLARATIONS
  imports TRANSLATE-FUNCTION-RULES
  imports REMOVE-FRONTEND-DECLARATIONS
  imports FILE-UTIL








  rule <k> #parseCommandLine(kompile, PGM)
        => PGM ~> #ekorePipeline ~> #filterKoreDeclarations
           ...
       </k>







  rule <k> #parseCommandLine(kast PATH, PGM)
        => PGM ~> #kastPipeline(token2String(PATH))
           ...
       </k>










  rule <k> #parseCommandLine(frontend-to-ekore, PGM)
        => PGM ~> #frontendPipeline
           ...
       </k>








  rule <k> #parseCommandLine(ekore-to-kore, PGM)
        => PGM ~> #ekorePipeline
           ...
       </k>



  syntax KItem ::= "#success"
  rule <k> P:Pattern ~> (#success => .K) ... </k>
       <exit-code> _ => 0 </exit-code>
  rule <k> #success => .K ... </k>
       <exit-code> _ => 0 </exit-code>






  syntax String ::= tokenToString(Any) [function, functional, hook(STRING.token2string)]
  syntax KItem ::= "#kastPipeline" "(" String ")"
  rule PGM:Any ~> #kastPipeline(PATH:String)
    => parseOuter(tokenToString(PGM))
    ~> #defnToConfig
    ~> #flattenProductions
    ~> #collectPgmGrammar
    ~> #parseProgramPath(PATH)
    ~> #success

  syntax KItem ::= "#ekorePipeline"
  rule #ekorePipeline
    => #parseToEKore
    ~> #defnToConfig
    ~> #flattenProductions
    ~> #nonFunctionProductionsToConstructors
    ~> #productionsToSortDeclarations
    ~> #productionsToSymbolDeclarations
    ~> #translateRules
    ~> #success
    
  syntax KItem ::= "#frontendPipeline"
  rule <k> PGM:Any ~> #frontendPipeline
    =>  parseOuter(
      //{readFile(DEPLOY_DIR +String "/src/inner.k")}:>String
      //+String
      tokenToString(PGM)
      ) // collect required files - hardcoded for now
    ~> #defnToConfig
    ~> #flattenProductions
    // parse bubbles
    ~> #createConfigGrammar
    ~> #parseConfigBubbles
    ~> #extractConfigInfo
    ~> #createRuleGrammar
    ~> #parseRuleBubbles
    ~> #success
    </k>
    <kinkDeployedDir> DEPLOY_DIR </kinkDeployedDir>



endmodule


