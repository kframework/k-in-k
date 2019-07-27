# sharpparse

This is a Haskell parser meant to parse a grammar written in K and produce
a parser using `happy` that will return KAST.

It runs it two stages: the parser generator reads a K file and generates
a corresponding `happy` file.  Currently this resides in `src/Grammar2.y`.

The second stage involves compiling `Grammar2` into a `parse` executable
which then can parse a file written in the specified grammar.

## Running

To run this, use the `sharpparse.sh` script.  The first argument will be
the K specification, the second is the input you want to parse, and the
third (optional) argument is the start symbol.

```
./sharpparse.sh test-data/test1.k test-data/test1-1.in Foo
```

If you want to specify a start symbol, you can do that with an argument to
the `parser-generator` executable.  For example, `test4.k` has this code:

```
syntax Nat ::= Nat "+" Nat     [klabel ( plus  )]
syntax Nat ::= "s" "(" Nat ")" [klabel ( succ  )]
syntax Nat ::= "."             [klabel (zero)]

syntax Foo ::= Foo "+" Foo     [klabel ( fooplus  )]
syntax Foo ::= "s" "(" Foo ")" [klabel ( foosucc  )]
syntax Foo ::= "."             [klabel (foozero)]
```

The test data `test4-1.in` has this:

```
s(s(.))  + s(s(.))
```

If you don't specify a start symbol, the first token defined will be taken
as start.  In this case, `Nat`.

```
% ./sharpparse.sh test-data/test4.k test-data/test4-1.in
"plus { } (succ { } (succ { } (zero { } ())),succ { } (succ { } (zero { } ())))"
```

But if we specify `Foo` instead, we get this:

```
% ./sharpparse.sh test-data/test4.k test-data/test4-1.in Foo
"fooplus { } (foosucc { } (foosucc { } (foozero { } ())),foosucc { } (foosucc { } (foozero { } ())))"
```

# Details

The file `Grammar.y` is the grammar to parse K syntax declarations.
This should not need to be modified in day-to-day operations.

The executable `parse` will parse a given K syntax specification on
`STDIN` and output a `happy` compatible grammar file.  It is intended
that you copy this over `Grammar2.y` and run `stack ghc` again.
For some reason `stack build` does not work well with `happy` when
GLR mode is activated.

The nice thing is that if you parse the same grammar more than once
the build stage detects this and doesn't have to recompile anything.

## Test Data

The test data has three kinds of files.  The `.k` files are the syntax
declarations.  The `.in` files contain code in the given language.
The `.out` files are the KAST parses.
