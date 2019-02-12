K Semantics of K
================

In this repository, we formally define the translation of the K Frontend
Language into axioms in Matching Logic, the logic over which the semantics of
the K Framework are defined. K being a Language used in formal verification, it
is important the K frontend constructs have clearly defined semantics.

After installing python3, [ninja-build] and [pandoc] simply run `./build`.

[pandoc]:      https://pandoc.org
[ninja-build]: https://ninja-build.org

Project Milestones
==================

Frontend to KORE
----------------

1.  Extend EKORE to allow bubbles (using k-light's parser)
2.  `#parse`

    1.  Generate grammar needed for `#parse` (Configuration grammar, Rule
        grammar)
    2.  `#parse` takes list of productions, string to parse, and start symbol

3.  Disambiguation

EKORE to KORE transformations
-----------------------------

1.  (Done) foobar: Get a module with only function symbols working.

    1.  ~~Define sorts~~
    2.  ~~Define symbols~~
    3.  ~~Translate function axioms~~

2.  Arithmetic Expressions:

    1.  ~~Identify exactly what axioms are needed for the haskell backend to
        exectute definitions~~
    2.  ~~Generalize sorts declaration code~~
    3.  ~~Generalize symbols declaration code~~
    4.  ~~Generalize function axioms~~
    5.  Desugar `syntax` declarations with multiple productions,
        into multiple `syntax` declarations with one production.
        Multiple passes will become easier in this format (passing grammars
        to the parser, declaring symbols, and adding function and constructor
        axioms).
    5.  Add `functional` & `constructor` axioms to all non-function productions.
    6.  (Not needed for execution semantics) Define functional and no-junk/mu axioms for
        constructors

3.  Imp:

    1.  Get rewrites working when configuration is pre-concretized for every
        rule.
    2.  Concretize configuration / Use contexts

Other important features
------------------------

1.  Error messages
2.  A more K-style implementation: More configuration/cell/matching based rules,
    fewer functions and iteration.

Testing
=======

End-to-end tests
----------------

Each folder is the `t/` directory defines a language. For each language we have
two tests for the EKORE pipeline:

1. That we generate the expected final ekore from the ekore with kasted bubbles
2. That the ekore pipeline is the identity over the expected ekore

In addition, there are additional tests to check that we can execute programs
in each of those languages.

For each language we can run all these tests using `./build t/<lang>` (e.g.
`./build t/foobar`)

To run a single test, (e.g. `t/foobar/<TEST>.ekore`), run
`./build .build/t/foobar/<TEST>.ekore.krun.kore.test`. If you need to see
the generated configuration, run
`cat .build/t/foobar-<TEST>.ekore.krun`.

Unit tests
----------

In addition, unit-tests are implemented using reachability logic in the
`unit-tests.md` file, and can be run via `./build unit-tests`.

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

Issues?
=======

Extending Kore's wellformedness to K's
--------------------------------------

K allows using `Sort`s before they are declared (so long as they are declared
later in the module). However, kore more strict:

> 3.  Every declared symbol or alias should have their argument sorts and return
>     sorts declared;
> 4.  All sorts, symbols, and aliases should be declared before being used;

Is it OK to assume that this holds in K-Definitions too for now?

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

