stack build 
if [ $? -ne 0 ]; then
    echo BUILD FAILED
    exit 1
fi

stack exec parser-generator $3 < $1 > parser/Grammar2.y
if [ $? -ne 0 ]; then
    echo INITIAL PARSE FAILED
    exit 1
fi

happy -i -l parser/Grammar2.y
(cd parser ; stack ghc -- -cpp -o ../parse --make Main.hs)

if [ $? -ne 0 ]; then
    echo PARSER COMPILE FAILED
    echo Investigate src/Grammar2.y, then do
    echo cp src/Grammar2-reference.y src/Grammar2.y
    exit 1
fi

./parse < $2
