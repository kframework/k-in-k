module Lib
--    ( someFunc
--    , getTokens
--    )
where

import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as H
import Data.List (find, intercalate)
import Production

someFunc :: IO ()
someFunc = putStrLn "someFunc"

isTerm :: Symbol -> Bool
isTerm (T _) = True
isTerm _     = False

isNonTerm :: Symbol -> Bool
isNonTerm (NT _) = True
isNonTerm _      = False

tokenNames :: H.HashMap String String
tokenNames = H.fromList [("(","LeftParen")
                         ,(")","RightParen")
                         ,("[","LeftBracket")
                         ,("]","RightBracket")
                         ,("{","LeftBrace")
                         ,("}","RightBrace")
                         ,("+","Plus")
                         ,("-","Minus")
                         ,("*","Times")
                         ,("/","Divide")
                         ,("#","Sharp")
                         ,(",","Comma")
                         ,(".","Period")
                         ]

getTokens :: [Production] -> [String]
getTokens plist = aux plist S.empty
   where aux [] tokenSet = S.toList tokenSet
         aux ((Production _ rhs _):ps) tokenSet =
           aux ps $ foldl (\set (T elt) -> S.insert elt set) tokenSet (filter isTerm rhs)

tokenName :: String -> String
tokenName t =
  case H.lookup t tokenNames of
    Just v -> "Token" ++ v
    Nothing -> "Token_" ++ t

getNonterms :: [Production] -> [String]
getNonterms plist = S.toList $ foldl (\set (Production nt _ _) -> S.insert nt set) S.empty plist

genTokenDecl :: [String] -> String
genTokenDecl tokens =
  concatMap (\t -> "    '" ++ t ++ "'   { " ++ tokenName t ++ " }\n") tokens
  where header = "%token\n"

genTokenData :: [String] -> String
genTokenData tokens = 
  "data Token = TokenId String\n" ++ concatMap (\t -> "           | " ++ tokenName t ++"\n") tokens ++ "   deriving (Eq,Ord,Show)\n\n"
  
isKLabel :: Attribute -> Bool
isKLabel (KLabel _) = True
isKLabel _          = False

getKLabel (Production nt _ attributes) =
  case find isKLabel attributes of
    Just (KLabel kl) -> kl
    Nothing -> nt

showSymbol :: Symbol -> String
showSymbol (NT s) = s
showSymbol (T s) = "'" ++ s ++ "'"

genAction :: Production -> String -> String
genAction p@(Production nt symbols attrs) kl =
  let showNonterms (T _) i = ""
      showNonterms (NT _) i = "$" ++ show i
      symbolList = case intercalate ",\",\"," (filter (/= "") $ zipWith showNonterms symbols (enumFrom 1)) of
        "" -> "\"\""
        x  -> x
  in concat [ "concat [\""
            , kl
            , " { } (\", "
            , symbolList
            , ", \")\"]"]

-- genOutput p(Production nt symbols attrs) =
--    concat [ "output (idx1,idx2,G_" ++ nt ++ ") = 

genProduction p@(Production l symbols attributes) =
  let kl = getKLabel p
   in concat [ l
             , ": "
             , intercalate " " (map showSymbol symbols)
             , "  { "
--             , (genAction p kl)
             , " } "]

outputHeader =
  concat [ "blookup fid m = let Just x = Map.lookup fid m in fmap b_nodes x"
         , "\n"
         ]

genOutputPattern p@(Production nt symbols attrs) =
  let kl = getKLabel p
   in concat [ "output [["
             , intercalate "," $ zipWith (\n t -> "b" ++ show n ++ "@(_,_," ++ t ++ ")")
                                         [1..] glrSymbols
             , "]] m =\n"
             , "    \"" ++ kl
             , subtreeArgs
             , "\n"]
  where getGLRsym (T x) = "HappyTok " ++ tokenName x
        getGLRsym (NT x) = "G_" ++ x
        glrSymbols = map getGLRsym symbols
        -- the indices of things that will be arguments
        treeIndices = map fst $ filter (\(a,b) -> isNonTerm b) $ zip [1..] symbols
        subtreeArgs = case length treeIndices of
          0 -> "\""
          _ -> concat [ "(\" ++ "
                      , intercalate " ++ \",\" ++ " $
                        map (\i -> "output (blookup b" ++ show i ++ " m) m") treeIndices
                      , "++ \")\""
                      ]

outputFooter =
  concat [ "output (x:y:ys) m = \"amb(\" ++ output [x] m ++ \",\" ++ output (y:ys) m ++ \")\"\n"
         , "output x m = error $ \"Unrecognized productions: \" ++ show x"]

-- output [[ b1@(_,_,HappyTok Token_s)
--         , b2@(_,_,HappyTok TokenLeftParen)
--         , b3@(_,_,G_Foo)
--         , b4@(_,_,HappyTok TokenRightParen)]] m =
--   "foosucc(" ++ output (blookup b3 m) m ++ ")"

happyHeader =
  concat [ "{\n"
         , "module Grammar2 where\n"
         , "import Data.Char\n"
         , "import qualified Data.Map as Map\n"
         , "}\n"
         , "\n"
         , "%name kinkgrammar\n"
         , "%tokentype { Token }\n"
         , "%error { parseError }\n\n"
         , "%token\n"]

happyMedium =
  concat [ "{\n"
         , "parseError :: [Token] -> a\n"
         , "parseError x = error (\"Parse error: \" ++ show x)\n"
         ]

lexerBegin =
  concat [ "lexId [] = (\"\",[])\n"
         , "lexId (c:xx) | isAlpha c =\n"
         , "  let (result,rest) = span isAlphaNum xx\n"
         , "   in (c:result, rest)\n"
         , "\n"
         , "eatws (c:xs) | isSpace c = eatws xs\n"
         , "eatws xx = xx\n"
         , "\n"
         , "lexer :: String -> [Token]\n"
         , "lexer [] = []\n"
         , "lexer (c:xs)  | isSpace c = lexer xs"]

lexSymbols tokens =
   concat ["lexer ('" ++ t ++ "':xs) = " ++ tokenName t ++ ": lexer xs\n" | t <- tokens, H.member t tokenNames]

lexTerminals tokens =
   concat ["    (\"" ++ s ++ "\",xs) -> " ++ tokenName s ++ " : lexer (eatws xs)\n" | s <- tokens, not (H.member s tokenNames)]
