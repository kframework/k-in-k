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

output [x,y] m = "amb(" ++ output [x] m ++ "," ++ output [y] m ++ ")"
output x m = error $ "Unrecognized productions: " ++ show x
