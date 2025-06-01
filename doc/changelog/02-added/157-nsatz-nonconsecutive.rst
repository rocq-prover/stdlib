- in `NsatzTactic`

  + Added support for `nsatz` using ring hypotheses above non-ring hypotheses.
    If a proof relies on `nsatz` not using earlier ring hypotheses, clear these
    hypotheses before calling nsatz.
    (`#157 <https://github.com/coq/stdlib/pull/157>`_,
    by Andres Erbsen).

