Internal Structure of Stdlib
============================

For historical reasons, the internal dependency structure of the
Stdlib library does not match its directory structure. That is, one
can find many exmaples of files in some directory `A` that depends
from files in another directory `B`, whereas other files in `B`
depends from files in `A`. This makes it difficult to understand what
are the acceptable dependencies in a given file, with developers left
trying adding dependencies until a circular dependency appears,
further worsening the current mess.

For backward compatibility reasons, that unfortunate state of affairs
cannot be easily fixed. However, to better understand the current
dependencies and mitigate the issue, we document here current tools to
help somewhat master that situation.

Documentation
-------------

One can find a graph of dependencies in file
`doc/stdlib/depends.dot`. This graph is included in the documentation
built by `make stdlib-html` in directory
`_build/default/doc/stdlib/html/`. To find the exact files contained
in each node `<n>` of this graph, one can look at the corresponding
`theories/Make.<n>` file.

CI testing
----------

A CI job `stdlib-subcomponents` checks that the above documented
structure remains valid.

How to Modify the Structure
---------------------------

When adding a file, it is enough to list it in the appropriate
`theories/Make.*` file. Note that, for historical reasons, some
directories are split between different subcomponents. In this case,
the new line in the `theories/Make.*` file must contain the
appropriate `_SubComponent` fake subdirectory. Look at
`theories/Make.lists` for an example.

To add or remove a subcomponent, just add or remove the corresponding
`theories/Make.*` file and adapt `doc/stdlib/depends.dot` and
`.nix/rocq-overlays/stdlib-subcomponents/default.nix`. One can use the
`dev/tools/make-depends.sh` script to help update the graph (the line
below `File dependencies` can be uncommented to better understand
which files are responsible for some subcomponent dependency).
