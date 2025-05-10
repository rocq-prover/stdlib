- in `ZArith,v` and dependencies

  + Reducing reliance on :g:`Znumtheory` within stdlib changed the internal
    dependencies between files, code relying on files being transitively
    required in stdlib may need to now explicitly ``Require``
    `Znumtheory`,
    `BinInt`,
    `BinList`,
    `BinNat`,
    `BinNums`,
    `BinPos`,
    `Setoid`,
    `Tauto`,
    `Zhints`,
    `Zpow_def`,
    `Zpow_facts`,
    or `Zbool`
    (`#136 <https://github.com/coq/stdlib/pull/136>`_,
    by Andres Erbsen).

