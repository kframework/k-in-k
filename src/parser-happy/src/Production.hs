module Production where

data Production = Production String [Symbol] [Attribute]
  deriving Show

data Symbol = NT String | T String
  deriving Show

data Attribute = Function
               | KLabel String
  deriving Show
