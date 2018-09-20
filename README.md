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
