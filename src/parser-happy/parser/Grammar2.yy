{
module Grammar2 where
import Data.Char
import qualified Data.Map as Map
import Data.List (intercalate)
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

test G_Grm = "Grm"

blookup fid m = let Just x = Map.lookup fid m in fmap b_nodes x

varName (a,b,G_Nat) = "G_Nat_" ++ show a ++ "_" ++ show b
varName (a,b,G_Foo) = "G_Nat_" ++ show a ++ "_" ++ show b
varName (a,b,HappyTok TokenPlus) = "Tok_Plus" ++ show a ++ "_" ++ show b
varName (a,b,HappyTok Token_s) = "Tok_s" ++ show a ++ "_" ++ show b
varName (a,b,HappyTok TokenLeftParen) = "Tok_lp" ++ show a ++ "_" ++ show b
varName (a,b,HappyTok TokenRightParen) = "Tok_rp" ++ show a ++ "_" ++ show b
varName (a,b,HappyTok TokenPeriod) = "Tok_p" ++ show a ++ "_" ++ show b

nodeVarName n i = varName n ++ "_" ++ show i

output name fid tree m =
  let (this,kids) = outputTree fid [tree] m
   in concat [output kidName undefined kidTree m | (kidName,kidTree) <- kids] 
      ++ name ++ " = " ++ this ++ ";\n\n"

outputTreeLookup fid m = outputTree fid (blookup fid m) m

outputTree _ [[b1@(_,_,G_Nat),b2@(_,_,HappyTok TokenPlus),b3@(_,_,G_Nat)]] m =
    let (t1,k1) = outputTreeLookup b1 m
        (t3,k3) = outputTreeLookup b3 m
     in ("plus(" ++ t1 ++ "," ++ t3 ++ ")", k1 ++ k3)

outputTree _ [[b1@(_,_,HappyTok Token_s),b2@(_,_,HappyTok TokenLeftParen),b3@(_,_,G_Nat),b4@(_,_,HappyTok TokenRightParen)]] m =
    let (t3,k3) = outputTreeLookup b3 m
     in ("succ(" ++ t3 ++ ")", k3)

outputTree _ [[b1@(_,_,HappyTok TokenPeriod)]] m =
    ("zero",[])

outputTree _ [[b1@(_,_,G_Foo),b2@(_,_,HappyTok TokenPlus),b3@(_,_,G_Foo)]] m =
    let (t1,k1) = outputTreeLookup b1 m
        (t3,k3) = outputTreeLookup b3 m
     in ("foo(" ++ t1 ++ "," ++ t3 ++ ")", k1 ++ k3)

outputTree _ [[b1@(_,_,HappyTok Token_s),b2@(_,_,HappyTok TokenLeftParen),b3@(_,_,G_Foo),b4@(_,_,HappyTok TokenRightParen)]] m =
    let (t3,k3) = outputTreeLookup b3 m
     in ("foosucc(" ++ t3 ++ ")", k3)

outputTree _ [[b1@(_,_,HappyTok TokenPeriod)]] m =
    ("foozero",[])

outputTree fid (r@(x:y:ys)) m = 
   let vars = zipWith (\ _ i -> nodeVarName fid i) r [1..]
    in ( "amb(" ++ intercalate "," vars ++ ")"
       , zip vars r)

outputTree x _ _ = error $ "Unrecognized productions: " ++ show x

        

}

