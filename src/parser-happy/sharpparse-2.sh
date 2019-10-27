# This doesn't re-create Grammar2.y

happy -i -l parser/Grammar2.y
(cd parser ; stack ghc -- -cpp -o ../parse --make Main.hs)

if [ $? -ne 0 ]; then
    echo PARSER COMPILE FAILED
    echo Investigate src/Grammar2.y, then do
    echo cp src/Grammar2-reference.y src/Grammar2.y
    exit 1
fi

./parse < $2
