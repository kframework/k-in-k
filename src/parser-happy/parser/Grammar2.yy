-- This is a hand generated parser to test the concepts out.

{
module Grammar2 where
import Data.Char
import qualified Data.Map as Map
}

%name kinkgrammar
%tokentype { Token }
%error { parseError }

%token

    '+'   { TokenPlus }
    '.'   { TokenPeriod }
    's'   { Token_s }
    '('   { TokenLeftParen }
    ')'   { TokenRightParen }


%%

Grm: Foo { }

Nat: Nat '+' Nat  {  } 
Nat: 's' '(' Nat ')'  {  } 
Nat: '.'  {  } 
Foo: Foo '+' Foo  {  } 
Foo: 's' '(' Foo ')'  {  } 
Foo: '.'  {  } 

{
parseError :: [Token] -> a
parseError x = error ("Parse error: " ++ show x)


data Token = TokenId String
           | TokenPlus
           | TokenPeriod
           | Token_s
           | TokenLeftParen
           | TokenRightParen
   deriving (Eq,Ord,Show)


lexId [] = ("",[])
lexId (c:xx) | isAlpha c =
  let (result,rest) = span isAlphaNum xx
   in (c:result, rest)

eatws (c:xs) | isSpace c = eatws xs
eatws xx = xx

lexer :: String -> [Token]
lexer [] = []
lexer (c:xs)  | isSpace c = lexer xs
lexer ('+':xs) = TokenPlus: lexer xs
lexer ('.':xs) = TokenPeriod: lexer xs
lexer ('(':xs) = TokenLeftParen: lexer xs
lexer (')':xs) = TokenRightParen: lexer xs

lexer xx = case lexId xx of
    ("",xs) -> [] -- handles eof
    ("s",xs) -> Token_s : lexer (eatws xs)
    ("END",xs) -> [] -- handles eof
    (s,xs) -> TokenId s : lexer xs

blookup fid m = let Just x = Map.lookup fid m in fmap b_nodes x

output [[ b1@(_,_,HappyTok Token_s)
        , b2@(_,_,HappyTok TokenLeftParen)
        , b3@(_,_,G_Foo)
        , b4@(_,_,HappyTok TokenRightParen)]] m =
  "foosucc(" ++ output (blookup b3 m) m ++ ")"

output [[ b1@(_,_,HappyTok TokenPeriod)]] m = "foozero"

output [[ b1@(_,_,G_Foo)]] m = output (blookup b1 m) m
output [[b1@(_,_,G_Foo),b2@(_,_,HappyTok TokenPlus),b3@(_,_,G_Foo)]] m =
  "fooplus(" ++ output (blookup b1 m) m ++ "," ++ output (blookup b3 m) m ++ ")"

output (x:y:ys) m = "amb(" ++ output [x] m ++ "," ++ output (y:ys) m ++ ")"
output x m = error $ "Unrecognized productions: " ++ show x
}

