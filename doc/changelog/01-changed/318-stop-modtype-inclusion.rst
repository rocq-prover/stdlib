- in `MSets, Numbers, Structures`

  + several module types were turned into plain modules to
    accomodate for rocq-prover/rocq#22580. The major difference
    is that they cannot be used as sealing adscriptions anymore.
    In order to ease the transition, corresponding module types
    were added alongside with the standard naming scheme Module
    Foo ↦ Module Type FooT
    (`#318 <https://github.com/coq/stdlib/pull/318>`_,
    by Pierre-Marie Pédrot).
