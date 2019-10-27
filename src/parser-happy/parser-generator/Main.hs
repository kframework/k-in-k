module Main where

import Lib
import Production
import Grammar
import System.Environment

main :: IO ()
main = do
   c <- getContents
   let k = (kgrammar . lexer) c
   let tokens = getTokens k
   let nonTerms = getNonterms k

   -- Print out header
   putStrLn happyHeader

   -- Print out tokens
   putStrLn (genTokenDecl tokens)
   putStrLn "\n%%\n"

   -- Generate Grammar
   let prods = map genProduction k

   -- Check for start symbol
   args <- getArgs

   let start = case (args,head k) of
                 (x:xs, _)               -> x
                 ([]  , Production l _ _)  -> l

   putStrLn $ "Grm: " ++ start ++ " { }\n"
   mapM putStrLn (map genProduction k)
   putStrLn ""

   -- Print out lexer
   putStrLn happyMedium
   putStrLn ""

   -- Print out token data type
   putStrLn $ genTokenData tokens

   -- Print out the lexer
   putStrLn lexerBegin
   putStrLn $ lexSymbols tokens
   putStrLn "lexer xx = case lexId xx of"
   putStrLn "    (\"\",xs) -> [] -- handles eof"
   putStr   $ lexTerminals tokens
   putStrLn "    (\"END\",xs) -> [] -- handles eof"
   putStrLn "    (s,xs) -> TokenId s : lexer xs"
   putStrLn ""
   putStrLn "test G_Grm = \"Grm\""

   putStrLn ""

   -- Print out the output generator
   putStrLn (outputHeader nonTerms tokens)

   mapM putStrLn (map genOutputPattern k)

   putStrLn outputFooter
   putStrLn "}\n"
   return ()
