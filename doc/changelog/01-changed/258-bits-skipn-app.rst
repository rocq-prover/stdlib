- in `theories/Zmod/Bits.v`

  + Fixed lemma `bits.skipn_app` to actually describe the interaction between
    the titular functions. Developments relying on the previous tautological
    statement can resore it by adding that version of the lemma to the codebase
    (`#258 <https://github.com/coq/stdlib/pull/258>`_,
    by Andres Erbsen).
