module Main where

-- import Lib
import Grammar2
import Grammar2Data
import qualified Data.Map as Map

main :: IO ()
--main = getContents >>= print . kinkgrammar . lexer
main = do
      s <- getContents
      case kinkgrammar $ map (:[]) $ lexer s of
        ParseOK r f -> do
                          let rr = head (head (blookup r f))
                          putStrLn $ "Ok " ++ show r ++ "\n"
                          putStrLn "Testing..."
                          putStrLn $ output (blookup rr f) f
        ParseEOF f  -> do
                          putStrLn $ "Premature end of input:\n"
                                      ++ unlines (map show $ Map.toList f)
        ParseError ts f -> do
                          putStrLn $ "Error: " ++ show ts

