
```k
require "inner.k"


module RULE-CELLS
  imports KCELLS
  imports RULE-LISTS
  // if this module is imported, the parser automatically
  // generates, for all productions that have the attribute 'cell' or 'maincell',
  // a production like below:
  //syntax Cell ::= "<top>" #OptionalDots K #OptionalDots "</top>" [klabel(<top>)]

  syntax #OptionalDots ::= "..." [klabel(#dots)]
                         | ""    [klabel(#noDots)]
endmodule

module REQUIRES-ENSURES
  imports BASIC-K

  syntax #RuleBody ::= K

  syntax #RuleContent ::= #RuleBody                                 [klabel("#ruleNoConditions")]
                        | #RuleBody "requires" K                    [klabel("#ruleRequires")]
                        | #RuleBody "ensures"  K                    [klabel("#ruleEnsures")]
                        | #RuleBody "requires" K "ensures" K        [klabel("#ruleRequiresEnsures")]
endmodule

// To be used to parse semantic rules
module K
  imports KSEQ-SYMBOLIC
  imports REQUIRES-ENSURES
  imports K-SORT-LATTICE
  imports AUTO-CASTS
  imports AUTO-FOLLOW

  syntax KBott ::= K "=>" K [klabel(#KRewrite), poly(0, 1, 2), non-assoc]
endmodule

module RULE-INNER // main parsing module for rules, start symbol: #RuleContent
  imports K
  imports RULE-CELLS
  imports DEFAULT-LAYOUT
endmodule
```
