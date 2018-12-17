K Semantics of K
================

In this repository, we formally define the translation of the K Frontend
Language into axioms in Matching Logic, the logic over which the semantics of
the K Framework are defined. K being a Language used in formal verification, it
is important the K frontend constructs have clearly defined semantics. We choose
to implement this translation in K itself, since becoming a self-hosting

After installing python3, [ninja-build] and [pandoc] simply run `./build`.

[pandoc]:      https://pandoc.org
[ninja-build]: https://ninja-build.org

Testing
=======

In each of the test files `t/foobar-<FEATURE>.ekore` uses a single additional
feature over the expected `kore0` syntax (for example: frontend modules, syntax
declarations, rules, contexts...). We expect all these to reduce down to [the
same expected output](t/foobar.ekore.expected). Eventually we want this expected
file to be `kore0`.

To run a single test, (e.g. `t/foobar-<FEATURE>.ekore`), run
`./build .build/t/foobar-<FEATURE>.ekore.krun.kore.test`. If you need to see
the generated configuration, run
`cat .build/t/foobar-<FEATURE>.ekore.krun`.

To run all `foobar` tests, run `./build t/foobar`

Getting started writing transformations
=======================================

Most transformations will use the infrastructure for iterating over declarations
in modules, documented [here](./kink.md#visitor-infrastructure).
[A concrete  example](./kink.md#collect-declared-sorts)
is documented in detail here to help new developers get started.

Style guidelines:

-   Align text to 80 characters.
-   Align code to 100 characters.
-   There must be exactly one newline before and after code blocks; and no
    consecutive empty lines (this causes line numbers in tangle output to differ
    from the actual line numbers and costs developer time).
-   Implement each transformation in a module of its own (e.g.
    `CONCRETIZE-CONFIGURATION`). If the transformation adds a symbol to the
    pipeline this should be the same as the module name, but in camel case (e.g.
    `#concretizeConfiguration`).

Pipeline stages
===============

TODO: Choose better names for `EKore-0`, ...

1.  Frontend K

    -   Includes:
        -   K Frontend syntax for defining grammar, rules, configuration
        -   Rules may use:
            -   User defined syntax (concrete syntax)
            -   KAST syntax (abstract syntax)
    -   Eliminate User defined syntax by converting to KAST
    -   Choose KLabels for each production
    -   `#bubble(...)` is replaced with KAST syntax
    -   Disabiguation
    -   `require "file.k"` should be expanded to the contents of the file.
    -   ...

2.  Extended-Kore 

    *   (EKore-0 -> EKore-1)  : Turn `#KProduction`s into kore `sort` declarations
    *   (EKore-1 -> EKore-2)  : `#KProduction`s replaced with kore's `symbol` declaration
    *   (EKore-2 -> EKore-3)  : Rules for functional symbols become axioms (of the form equations, not rewrites).
    *   (EKore-? -> EKore-?)  : Other rules for symbols become `\rewrites` with contexts
    *   Define configuration cell sorts ...
    *   ...

3.  Pre-Kore : No more K frontend constructs
    -   Generate "No Junk" Axioms
    -   Generate Functional Axioms
    -   Generate Strictness Axioms
    -   Generate Configuration init functions
    -   Configuration concretization
    -   ...


Interesting files
-----------------

In the `imp/imp.ekore0` we sketch out what we expect the `ekore0` syntax to look like.

* We Assume dotMap{}() and mapLookup{}(...)  are the symbols defined in `DOMAINS`

* We use `_/_` etc as sugar for Lbl'Unds'Div'Unds'{}()


Issues?
=======

`kore.k`
--------

-   `kore.k` says that `Name` is a `Sort`, but I think it should be a
    `SortVariable` instead? `kore-parse` throws: "Sort variable 'Foo' not
    declared" otherwise.
-   `kore.k` has sort names like `Declaration` whereas `kore-parse` calls its
    corresponding construct `ObjectSentence`s. I think we should converge?

ekore / `K-OUTER` syntax
------------------------

-   How will AC lookuPs look
-   Should `#KRequires(\dv{Bool{}("true"))` be `#KRequires(\top{..}())`
-   Why are bubbles inside `#NoAttrs` / `#Attrs`, can we instead have:

    `#KRule{}(#bubble(...), #KAttrs(#KAttrsEmpty(){}, #KRequires{}(...))`

K-light
-------

-   We expect top-level `requires "file.k"` to be handled and `domains.k` etc to
    be included in the definition.

