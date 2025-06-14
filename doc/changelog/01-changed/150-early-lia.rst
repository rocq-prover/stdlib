- Internal dependencies between about 50 stdlib files

  + To diagnose a failing qualified reference use
    `From Stdlib Require All. Locate My.Qualified.reference.`
    Then add a Require command for the appropriately granular containing file
    (`#150 <https://github.com/coq/stdlib/pull/150>`_,
    by Andres Erbsen).

