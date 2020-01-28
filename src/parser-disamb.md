```k
module DISAMBIGUATE
  imports KORE-ABSTRACT
  imports KORE-HELPERS
  imports K-PRODUCTION-ABSTRACT
  imports SET
  imports PARSER-UTIL


  syntax KItem ::= pair(KItem, KItem)
  syntax Pattern ::= disambiguate(Pattern, Set) [function]
  syntax Pattern ::= applyTypeCheck(Pattern, Map, Set, Set)
  
  // variables may already be cast in one or more places, so collect all the types
  syntax Set ::= collectCasts(Pattern) [function]
  syntax Set ::= collectCastsPs(Patterns) [function]
  syntax Set ::= collectCasts2(Pattern, String) [function]
  rule collectCasts(SName { _ } ( Ps )) => collectCastsPs(Ps)
    requires findString(tokenToString(SName:UpperName), "SemanticCastTo", 0) =/=Int 0
  rule collectCasts(SName { _ } ( P, .Patterns )) => collectCasts2(P, substrString(tokenToString(SName), 14, lengthString(tokenToString(SName))))
    requires findString(tokenToString(SName:UpperName), "SemanticCastTo", 0) ==Int 0
    
  rule collectCasts2(\dv{_}(VarName), SortName) => SetItem(pair(VarName, SortName))
  rule collectCasts2(P, _) => collectCasts(P) [owise] // means cast is over a normal production so continue with normal traversal

  rule collectCastsPs(P, Ps) => collectCasts(P) collectCastsPs(Ps)
  rule collectCastsPs(.Patterns) => .Set

  // make a map of subsorts
  syntax Set ::= getSubsorts(Set) [function]
  rule getSubsorts(SetItem(S) Ss:Set) => getSubsorts2(S) getSubsorts(Ss)
  rule getSubsorts(.Set) => .Set

  syntax Set ::= getSubsorts2(K) [function]
  rule getSubsorts2(kSyntaxProduction(S1:KSort, kProductionWAttr(nonTerminal(S2:KSort), _))) => SetItem(pair(S1, S2))
  rule getSubsorts2(_) => .Set [owise]
  
  syntax Set ::= tclosure(Set) [function]
  rule tclosure(SetItem(pair(A, B)) SetItem(pair(B, C)) R:Set) 
    => tclosure(SetItem(pair(A, B)) SetItem(pair(B, C)) SetItem(pair(A, C)) R:Set)
    requires notBool( pair(A, C) in R)
  rule tclosure(R) => R [owise]
  
  
  // make a map of klabel |-> list of sorts
  syntax Map ::= collectSignature(Map, Set) [function]
  syntax List ::= getSortArguments(KProduction) [function]
  syntax String ::= getKLabelFromArgs(K) [function]
  rule collectSignature(M => M [ getKLabelFromArgs(Args) <- ListItem(S1) getSortArguments(Pi) ], (SetItem(kSyntaxProduction(S1:KSort, kProductionWAttr(Pi, Args))) => .Set) S:Set )
  rule collectSignature(M, .Set) => M

  rule getSortArguments(kProduction(P1, P2)) => getSortArguments(P1) getSortArguments(P2)
  rule getSortArguments(nonTerminal(S2:KSort)) => ListItem(S2)
  rule getSortArguments(terminal(_)) => .List
  rule getSortArguments(regexTerminal(_)) => .List
  
  rule getKLabelFromArgs(noAtt) => ""
  rule getKLabelFromArgs(.AttrList) => ""
  rule getKLabelFromArgs(kAttributesDeclaration(A) => A)
  rule getKLabelFromArgs(consAttrList(tagContent(#token("klabel","LowerName"), KL), _)) => tokenToString(KL:LowerName)
  rule getKLabelFromArgs(consAttrList(_, A) => A) [owise]
  
  // isSubsorted
  syntax Bool ::= isSubsorted  (Sort, Sort, Set) [function]
  syntax Bool ::= isSubsortedEq(Sort, Sort, Set) [function]
  rule isSubsorted(S1, S2, S) => pair(S1, S2) in S
  rule isSubsortedEq(S1, S2, S) => S1 ==K S2 orBool isSubsorted(S1, S2, S)

  // apply 
  rule disambiguate(P, Prods) => applyTypeCheck(P, collectSignature(.Map, Prods), tclosure(getSubsorts(Prods)), collectCasts(P))
  
  // apply type check
  // checkType(<sort from top>, <term to apply on>, <signatures>, <subsort relations>, <types to enforce>)
  syntax Pattern  ::= checkType (Pattern,  KSort, Map, Set, Set)
  syntax Patterns ::= checkType2(Patterns, List,  Map, Set, Set)
  rule applyTypeCheck(P, Sigs, Subs, Types) => checkType(P, #token("K","UpperName"), Sigs, Subs, Types)
  rule checkType (SName { _ } ( Ps ), UpSort, ((SName |-> ListItem(SSort) Sig:List) _:Map) #as Sigs, Subs, Types)
    => checkType2(Ps, Sig, Sigs, Subs, Types)
   requires isSubsortedEq(UpSort, SSort, Subs)
  rule checkType2((P:Pattern, Ps:Patterns), ListItem(S) Sig, Sigs, Subs, Types)
    => checkType(P, S, Sigs, Subs, Types), checkType2(Ps, Sig, Sigs, Subs, Types)
  rule checkType2(.Patterns, .List, _, _, _)
    => .Patterns
  
  
  // TODO: apply type checking

endmodule
```
