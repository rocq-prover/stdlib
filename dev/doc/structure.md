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

Special `.v` files in `subcomponents/` are used to group the normal `.v` files under `theories/` into subcomponents.
A file in one subcomponent can only depend on a file in another subcomponent
if the former file's subcomponent depends on the latter file's subcomponent
(potentially through other subcomponents).
This rule, and the completeness of the subcomponent categorization,
are checked during `make stdlib-html` by `dev/tools/subcomponents.py`,
generating a dependency graph in `_build/default/doc/stdlib/index-subcomponents.html`.

How to Modify the Structure
---------------------------

When adding a file, it is sufficient to list it in the appropriate `subcomponents/*.v` file.
However, it is often preferable to instead `Require` the new file in an existing `.v` file documented in doc/stdlib/index.html`
(which is already assigned to the appropriate subcomponent).

`dev/tools/subcomponents.py` can be called directly to check that subcomponents are declared consistently and diagnose related issues.
