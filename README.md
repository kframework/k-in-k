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

    *   (EKore-0 -> EKore-1)  : Turn productions into kore `symbol` declarations
    *   (EKore-1 -> EKore-2)  : All sorts have `sort` declarations included
    *   (EKore-2 -> EKore-3)  : Productions replaced with kore's `symbol` declaration
    *   (EKore-3 -> EKore-3a) : Rules for functional symbols become axioms
    *   (EKore-3 -> EKore-3b) : Other rules for symbols become `\rewrites` with contexts
    *   ...

3.  Pre-Kore : No more K frontend constructs
    -   Generate "No Junk" Axioms
    -   Generate Functional Axioms
    -   Generate Strictness Axioms
    -   Configuration concretization
    -   ...

Issues?
=======

-   `kore.k` says that `Name` is a `Sort`, but I think it should be a
    `SortVariable` instead? `kore-parse` throws: "Sort variable 'Foo' not
    declared" otherwise.
-   `kore.k` has sort names like `Declaration` whereas `kore-parse` calls its
    corresponding construct `ObjectSentence`s. I think we should converge?

TODO:

-   Using `Sets` etc makes output non-deterministic (e.g. the order of
    statements may be permuted). This makes testing hard.
    

