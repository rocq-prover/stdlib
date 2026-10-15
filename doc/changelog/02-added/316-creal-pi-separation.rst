
- in `theories/Reals/Cauchy/PiWindowCore.v`, `theories/Reals/Cauchy/PiLeibnizCReal.v`,
  `theories/Reals/Cauchy/PiKernelSlack.v`, `theories/Reals/Cauchy/PiCompareT.v`
  and `theories/Reals/Cauchy/PiSeparation.v`

  + new files `PiWindowCore`, `PiLeibnizCReal`, `PiKernelSlack`, `PiCompareT` and
    `PiSeparation`, with definition `pi_leibniz` and theorem
    `pi_leibniz_strong_irrational` (a constructive pi for the constructive Cauchy
    reals, realized by the alternating Leibniz series and apart from every rational
    constant with explicit witnesses; assumption-free and extraction-pure; uses the
    escape-window engine `ConstructiveCauchyRealsSep`)
    (`#316 <https://github.com/rocq-prover/stdlib/pull/316>`_,
    fixes #315, by hy7pc8gfmf-dotcom).
