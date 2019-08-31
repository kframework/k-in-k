Predefined sorts and base K syntax

```k
// Module defining only the sorts K and KString, useful for modularity
module SORT-K
  syntax K
endmodule

module BASIC-K
  imports SORT-K
  syntax KItem
  syntax KConfigVar [token]
endmodule

module KSTRING
  syntax KString ::= r"[\\\"](([^\\\"\n\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]"      [token]
  // optionally qualified strings, like in Scala "abc", i"abc", r"a*bc", etc.
endmodule

module SORT-KBOTT
  imports SORT-K
  syntax KBott
endmodule

module KAST
  imports BASIC-K
  imports SORT-KBOTT
  imports KSTRING

  syntax KBott ::= "#token" "(" KString "," KString ")"  [klabel(kToken)]
                 | "#klabel" "(" KLabel ")"              [klabel(wrappedKLabel)]
                 | KLabel "(" KList ")"                  [klabel(kApply)]

  syntax KLabel ::= r"`(\\\\`|\\\\\\\\|[^`\\\\\n\r])+`"   [token]
                  | r"(?<![a-zA-Z0-9])[#a-z][a-zA-Z0-9]*" [token, autoReject]
                       // something that doesn't collide with meta-variables

  syntax KList ::= K
                 | ".KList"          [klabel(emptyKList)]
                 | KList "," KList   [klabel(kList), left, assoc, unit(emptyKList), prefer]
endmodule


// To be used when parsing/pretty-printing ground configurations
module KSEQ
  imports KAST
  syntax KBott ::= ".K"      [klabel(emptyK), unparseAvoid]
                 | K "~>" K  [klabel(kSequence), left, assoc, unit(emptyK)]
                 | "(" K ")" [bracket]
endmodule

// To be used when parsing/pretty-printing symbolic configurations
module KSEQ-SYMBOLIC
  imports KSEQ

  syntax KVariable  ::= r"(?<![A-Za-z0-9_\\$!\\?])(\\!|\\?)?([A-Z][A-Za-z0-9'_]*|_)"   [token, autoReject]
  syntax KConfigVar ::= r"(?<![A-Za-z0-9_\\$!\\?])(\\$)([A-Z][A-Za-z0-9'_]*)"          [token, autoReject]
  syntax KBott      ::= KVariable
  syntax KBott      ::= KConfigVar
  syntax KLabel     ::= KVariable
endmodule

module KCELLS
  imports KAST

  syntax Cell
  syntax Bag ::= Bag Bag  [left, assoc, klabel(cells), unit(cells)]
               | ".Bag"   [klabel(cells)]
               | Cell
  syntax Bag ::= "(" Bag ")" [bracket]
endmodule

module K-SORT-LATTICE
  imports SORT-KBOTT
  syntax K     ::= KItem
  syntax KItem ::= KBott
endmodule

module AUTO-CASTS
  // if this module is imported, the parser automatically
  // generates, for all sorts, productions of the form:
  // Sort  ::= Sort "::Sort"
  // Sort  ::= Sort ":Sort"
  // KBott ::= Sort "<:Sort"
  // Sort  ::= K    ":>Sort"
  // this is part of the mechanism that allows concrete user syntax in K
endmodule

module AUTO-FOLLOW
  // if this module is imported, the parser automatically
  // generates a follow restriction for every terminal which is a prefix
  // of another terminal. This is useful to prevent ambiguities such as:
  // syntax K ::= "a"
  // syntax K ::= "b"
  // syntax K ::= "ab"
  // syntax K ::= K K
  // #parse("ab", "K")
  // In the above example, the terminal "a" is not allowed to be followed by a "b"
  // because it would turn the terminal into the terminal "ab".
endmodule

module RULE-LISTS
  // if this module is imported, the parser automatically
  // adds the subsort production to the parsing module only:
  // Es ::= E        [userList("*")]

endmodule

module DEFAULT-LAYOUT
  syntax Layout ::= r"(/\\*([^\\*]|(\\*+([^\\*/])))*\\*+/|//[^\n\r]*|[\\ \n\r\t])*" [klabel(layout)]
endmodule

// To be used to parse terms in full K
module K-TERM
  imports KSEQ-SYMBOLIC
  imports K-SORT-LATTICE
  imports AUTO-CASTS
  imports AUTO-FOLLOW
endmodule
```

```k
module CONFIG-CELLS
  imports KCELLS
  imports RULE-LISTS
  syntax CellName ::= r"[a-zA-Z][A-Za-z0-9'_]*"   [token]

  syntax Cell ::= "<" CellName CellProperties ">" K "</" CellName ">" [klabel(configCell)]
  syntax Cell ::= "<" CellName "/>" [klabel(externalCell)]

  syntax CellProperties ::= CellProperty CellProperties [klabel(cellPropertyList)]
                          | ""                          [klabel(cellPropertyListTerminator)]
  syntax CellProperty ::= CellName "=" KString          [klabel(cellProperty)]

endmodule

module CONFIG-INNER // main parsing module for configuration, start symbol: K
  imports K-TERM
  imports CONFIG-CELLS
  imports DEFAULT-LAYOUT
endmodule
```

```k
module RULE-CELLS
  imports KCELLS
  imports RULE-LISTS
  // if this module is imported, the parser automatically
  // generates, for all productions that have the attribute 'cell' or 'maincell',
  // a production like below:
  //syntax Cell ::= "<top>" OptionalDots K OptionalDots "</top>" [klabel(<top>)]

  syntax OptionalDots ::= "..." [klabel(dots)]
                        | ""    [klabel(noDots)]
endmodule

module REQUIRES-ENSURES
  imports BASIC-K

  syntax RuleBody ::= K

  syntax RuleContent ::= RuleBody                                 [klabel("ruleNoConditions")]
                       | RuleBody "requires" K                    [klabel("ruleRequires")]
                       | RuleBody "ensures"  K                    [klabel("ruleEnsures")]
                       | RuleBody "requires" K "ensures" K        [klabel("ruleRequiresEnsures")]
endmodule

module DEFAULT-CONFIGURATION
  imports BASIC-K

  configuration <k> $PGM:K </k>
endmodule

// To be used to parse semantic rules
module K
  imports KSEQ-SYMBOLIC
  imports REQUIRES-ENSURES
  imports K-SORT-LATTICE
  imports AUTO-CASTS
  imports AUTO-FOLLOW

  syntax KBott ::= K "=>" K [klabel(KRewrite)]
endmodule

module RULE-INNER // main parsing module for rules, start symbol: RuleContent
  imports K
  imports RULE-CELLS
  imports DEFAULT-LAYOUT
endmodule
```
