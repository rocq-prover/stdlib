.. _changes:

--------------
Recent changes
--------------

.. ifconfig:: not is_a_released_version

   .. include:: ../unreleased.rst

Version 9.1
-----------

Changes in 9.1.0
~~~~~~~~~~~~~~~~

.. contents::
   :local:


Changed
^^^^^^^

- Internal dependencies between about 50 stdlib files

  + To diagnose a failing qualified reference use
    `From Stdlib Require All. Locate My.Qualified.reference.`
    Then add a Require command for the appropriately granular containing file
    (`#150 <https://github.com/coq/stdlib/pull/150>`_,
    by Andres Erbsen).

- in `FinFun`

  + Split out non-`Fin`-specific definitons into `Lists.Finite`
    (`#154 <https://github.com/coq/stdlib/pull/154>`_,
    by Andres Erbsen).

- in `HLevels.v`

  + Split into `HLevels` into `HLevelsBase`, which does not depend
    on axioms, and :g:`HLevels`, which exports the former and provides the
    previous functionality
    (`#133 <https://github.com/coq/stdlib/pull/133>`_,
    by Andres Erbsen).

- in `NsatzTactic.v`

  + Split NsatzTactic into a smaller `NsatzTactic` that only depends on
    `setoid_ring`, and per-domain files `ZNsatz`, `QNsatz`, and `RNsatz`
    (`#155 <https://github.com/coq/stdlib/pull/155>`_,
    by Andres Erbsen).

- in `Permutation`

  + Moved `Fin`-specific definitons into `FinFun`
    (`#154 <https://github.com/coq/stdlib/pull/154>`_,
    by Andres Erbsen).

- in `RIneq.v`

  + Changed the statement of `Rmult_gt_reg_l`.
    Use the convertible `Rmult_lt_reg_l`
    if you need a backward compatible solution
    (`#213 <https://github.com/coq/stdlib/pull/213>`_,
    fixes `#212 <https://github.com/coq/stdlib/issues/212>`_,
    by Damien Doligez).

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

Added
^^^^^

- in `BinInt`

  + Added lemmas `div_eucl_0_r`, `mod_0_r`, `div_0_r`
    (`#150 <https://github.com/coq/stdlib/pull/150>`_,
    by Andres Erbsen).

- in `BinNatDef.v` and `BinNat.v`

  + Added definition `Niter_op` for repeating associative operations, a proof
    relating it to the generic :g:`N.iter` (:g:`iter_op_correct`), and
    properties :g:`iter_op_0_r`, :g:`iter_op_1_r`, :g:`iter_op_succ_r`, and
    :g:`iter_op_add_r`
    (`#134 <https://github.com/coq/stdlib/pull/134>`_,
    by Andres Erbsen).

- in `Diaconescu.v`

  + Add a proof of Diaconescu's theorem assuming propositional
    extensionality rather than predicate extensionality
    (`#214 <https://github.com/coq/stdlib/pull/214>`_,
    by Jean Abou Samra).

- in `ENsatzTactic`

  + Add new tactic `ensatz` for proving polynomial equalities
    with existential quantifiers or existential variables
    (`#160 <https://github.com/coq/stdlib/pull/160>`_,
    by Lionel Blatter).

- in `HLevelsBase.v`

  + transparent lemmas :g:`false_hprop`, :g:`true_hprop`,
    :g:`Is_true_hprop`, :g:`eq_true_hprop`, and a wrappers
    :g:`transparent_Is_true` and :g:`transparent_eq_true` to produce
    transparent proofs for :g:`Is_true` and
    :g:`eq_true` given not necessarily transparent proofs of the same
    (`#133 <https://github.com/coq/stdlib/pull/133>`_,
    by Andres Erbsen).

- in `Ncring_tac`

  + Added extension-point typeclass `extra_reify` that is only resolved on
    non-variables for which built-in syntax-directed reification did not find a
    match
    (`#156 <https://github.com/coq/stdlib/pull/156>`_,
    by Andres Erbsen).

- in `NsatzTactic`

  + Added support for `nsatz` using ring hypotheses above non-ring hypotheses.
    If a proof relies on `nsatz` not using earlier ring hypotheses, clear these
    hypotheses before calling nsatz.
    (`#157 <https://github.com/coq/stdlib/pull/157>`_,
    by Andres Erbsen).

- in `ZArithRing`

  + Added `Zpower_theory` to replace the now-deprecated one in `Zpow_def`
    (`#150 <https://github.com/coq/stdlib/pull/150>`_,
    by Andres Erbsen).

- in `Zcong.v`

  + theory of integer congruences and multiplicative inverses up to Chinese
    Remainder Theorem
    (`#135 <https://github.com/coq/stdlib/pull/135>`_,
    by Andres Erbsen).

- new file `Zdivisibility.v`

  + Refactored theory of integer divisibility including primality and
    coprimality. This file is intended to replace `Znumtheory`
    (`#136 <https://github.com/coq/stdlib/pull/136>`_,
    by Andres Erbsen).

- in `Zmod.v`

  + Added theory of modular integer arithmetic, including machine words /
    bitvectors and the multiplicative group of integers modulo another integer.
    About 450 lemmas are provided
    (`#144 <https://github.com/coq/stdlib/pull/144>`_,
    by Andres Erbsen).

- in `ZmodNsatz` and `Zmod`

  + Added support for the `nsatz` tactic on `Zmod`
    (`#156 <https://github.com/coq/stdlib/pull/156>`_,
    by Andres Erbsen).

- in `ZModOffset.v`

  + Added theory of :g:`Z.modulo` with output range shifted by a constant. The
    main definition is :g:`Z.omodulo`, with :g:`Z.smodulo` capturing the
    special case where the offset is equal to half of the modulus, such as in
    two's-complement arithmetic
    (`#135 <https://github.com/coq/stdlib/pull/135>`_,
    by Andres Erbsen).

Removed
^^^^^^^

- in `Zdiv.v`

  + alias `Zmod` for `Z.modulo`, deprecated since 8.17
    (`#149 <https://github.com/coq/stdlib/pull/149>`_,
    by Andres Erbsen).

- in `ZMicromega`

  + Support for `EnumProof`s in `ZChecker`.
    The `lia` plugin does not generate such proofs anymore.
    If you have a different certificate generator that targets the same
    checker, please open an issue
    (`#150 <https://github.com/coq/stdlib/pull/150>`_,
    by Andres Erbsen).

Deprecated
^^^^^^^^^^

- in `Div`

  + Lemmas `Zmod_0_r` and `Zdiv_0_r` in favor of `BinInt.Z.mod_0_r` and
    `BinInt.Z.div_0_r`
    (`#150 <https://github.com/coq/stdlib/pull/150>`_,
    by Andres Erbsen).

- in `Rtauto and rtauto.Bintree`

  + If you use this plugin and would like to continue using it, please open an
    issue to discuss its maintainership
    (`#161 <https://github.com/coq/stdlib/pull/161>`_,
    by Andres Erbsen).

- in `ZMicromega`

  + Internal tactics `flatten_bool` and `inv`, definitions `EnumProof`, `isZ0`,
    `bdepth`, `vars`, and lemmas `eq_le_iff`, `isZ0_0`, `isZ0_0`, `isZ0_n0`,
    `isZ0_n0`, `eq_true_iff_eq`, `max_var_le`, `max_var_correct`,
    `max_var_nformulae_correct_aux`, `max_var_nformalae_correct`,
    `ltof_bdepth_split_l`, `ltof_bdepth_split_r`
    (`#150 <https://github.com/coq/stdlib/pull/150>`_,
    by Andres Erbsen).

  + Misplaced lemma `Zpower_theory`, with replacement in `ZArithRing`
    (`#150 <https://github.com/coq/stdlib/pull/150>`_,
    by Andres Erbsen).

- in `Znumtheory.v`

  + Deprecated most definitions in favor of `Zdivisibility.v` or appropriate
    established files
    (`#136 <https://github.com/coq/stdlib/pull/136>`_,
    by Andres Erbsen).

Version 9.0
-----------

Changes in 9.0.0
~~~~~~~~~~~~~~~~

.. contents::
   :local:

Changed
^^^^^^^

- Changed the requirement prefix of the standard library from ``Coq``
  to ``Stdlib`` and made it mandatory. As a temporary measure, for
  backward compatibility with older versions, ``Coq``, or a missing
  `From Stdlib`, is immediatly translated to ``Stdlib`` with a
  warning. It is thus not recommended to name anything ``Coq`` or
  ``Coq.*``. The recommended transition path is to first potentially
  silence the warnings, adding the lines
  ``-arg -w -arg -deprecated-from-Coq``,
  ``-arg -w -arg -deprecated-dirpath-Coq`` and
  ``-arg -w -arg -deprecated-missing-stdlib``
  or simply the more generic
  ``-arg -compat -arg 8.20`` to your ``_CoqProject``.
  Then, when droping support for Coq <= 8.20, replacing requirement of
  Stdlib modules by `From Stdlib Require {Import,Export,} <LibraryModules>.`.
  Beware that the Stdlib still has a handful redundant names, that is
  for modules `Byte`, you still have to use `From Stdlib.Strings` or
  `From Stdlib.Init`, for `Tactics` use `From Stdlib.Program`
  or `From Stdlib.Init`, for `Tauto` use `From Stdlib.micromega`
  or `From Stdlib.Init` and for `Wf`, use `From Stdlib.Program`
  or `From Stdlib.Init`
  (`#19310 <https://github.com/coq/coq/pull/19310>`_
  and `#19530 <https://github.com/coq/coq/pull/19530>`_,
  the latter starting to implement
  `CEP#83 <https://github.com/coq/ceps/pull/83>`_
  by Pierre Roux).

- in `Fin.v`

  + `case_L_R'` and `case_L_R` made transparent definitions
    (`#19655 <https://github.com/coq/coq/pull/19655>`_,
    by Andrej Dudenhefner).

- in `List.v`

  + lemmas that were using the letter :g:`O` in their name to refer to
    zero now use instead the digit :g:`0`
    (`#19479 <https://github.com/coq/coq/pull/19479>`_,
    by Hugo Herbelin).

- in several files

  + remove transitive requirements or export of theories about ``Z``,
    you may need to add explicit ``Require`` or ``Import``
    of :g:`ZArith` or :g:`Lia`
    (`#19801 <https://github.com/coq/coq/pull/19801>`_,
    by Andres Erbsen).

- in `Zbool.v`

  + definition of :g:`Zeq_bool` is now an alias for :g:`Z.eqb`,
    this is expected to simplify simultaneous compatibility with 8.20 and 9.0
    (`#19801 <https://github.com/coq/coq/pull/19801>`_,
    by Andres Erbsen).

Added
^^^^^

- file `All.v` which does `Require Export` of all other files in Stdlib
  (`#19914 <https://github.com/coq/coq/pull/19914>`_,
  by Gaëtan Gilbert).

- in `BinPos.v`

  + lemma :g:`BinPos.iter_op_correct`, relating :g:`Pos.iter_op` for
    associative operations to the more general :g:`Pos.iter`
    (`#19749 <https://github.com/coq/coq/pull/19749>`_,
    by Andres Erbsen).

- in `Eqdep_dec.v` in `Logic`

  + lemmas :g:`UIP_None_l`, :g:`UIP_None_r`, :g:`UIP_None_None`,
    :g:`UIP_nil_l`, :g:`UIP_nil_r`, :g:`UIP_nil_nil`
    (`#19483 <https://github.com/coq/coq/pull/19483>`_,
    by Andres Erbsen).

- in `EquivDec.v` in `Classes`

  + :g:`EqDec` instance for :g:`option`
    (`#19949 <https://github.com/coq/coq/pull/19949>`_,
    by Daniil Iaitskov).

- in `Fin.v`

  + lemmas `case_L_R'_L`, `case_L_R'_R`, `case_L_R_L`, `case_L_R_R`
    (`#19655 <https://github.com/coq/coq/pull/19655>`_,
    by Andrej Dudenhefner).

- in `Inverse_Image.v` in `Wellfounded`

  + lemmas `Acc_simulation` and `wf_simulation`
    (`#18183 <https://github.com/coq/coq/pull/18183>`_,
    by Andrej Dudenhefner).

- in `List.v`

  + lemmas `length_cons` and `length_nil`
    (`#19479 <https://github.com/coq/coq/pull/19479>`_,
    by Hugo Herbelin).

  + :g:`Proper` instance to enable :g:`setoid_rewrite` to rewrite
    inside the function argument of :g:`List.map`
    (`#19515 <https://github.com/coq/coq/pull/19515>`_,
    by Andres Erbsen).

  + lemmas :g:`length_tl`, :g:`tl_map`, :g:`filter_rev`,
    :g:`filter_map_swap`, :g:`filter_true`, :g:`filter_false`,
    :g:`list_prod_as_flat_map`, :g:`skipn_seq`, :g:`map_const`,
    :g:`fst_list_prod`, :g:`snd_list_prod`, :g:`Injective_map_NoDup_in`,
    and :g:`Permutation_map_same_l`
    (`#19748 <https://github.com/coq/coq/pull/19748>`_,
    by Andres Erbsen).

  + lemma `length_app_comm`
    (`#75 <https://github.com/coq/stdlib/pull/75>`_,
    by Nicholas Hubbard).

- file `List_Extension.v` in `Wellfounded`
  (`#18183 <https://github.com/coq/coq/pull/18183>`_,
  by Andrej Dudenhefner).

- in `List_Extension.v`

  + well-founded list extension `list_ext` of a well-founded relation,
    including infrastructure lemmas. It can be used for
    well-foundedness proofs such as `wf_lex_exp` in
    `Lexicographic_Exponentiation.v`
    (`#18183 <https://github.com/coq/coq/pull/18183>`_,
    by Andrej Dudenhefner).

- in `NatInt.v`

  + lemmas :g:`mul_reg_l` and :g:`mul_reg_r`
    (`#17560 <https://github.com/coq/coq/pull/17560>`_,
    by Remzi Yang).

- in `Operators_Properties.v` in `Relations`

  + lemma `clos_t_clos_rt`
    (`#18183 <https://github.com/coq/coq/pull/18183>`_,
    by Andrej Dudenhefner).

- in `Reals`

  + new file `Zfloor.v` with definitions of `Zfloor` and `Zceil`
    and corresponding lemmas `up_Zfloor`, `IZR_up_Zfloor`,
    `Zfloor_bound`, `Zfloor_lub`, `Zfloor_eq`, `Zfloor_le`,
    `Zfloor_addz`, `ZfloorZ`, `ZfloorNZ`, `ZfloorD_cond`, `Zceil_eq`,
    `Zceil_le`, `Zceil_addz`, `ZceilD_cond`, `ZfloorB_cond`,
    `ZceilB_cond`
    (`#89 <https://github.com/coq/stdlib/pull/89>`_,
    by Laurent Théry).

- in `VectorSpec.v`

  + lemma :g:`Forall2_cons_iff`
    (`#19269 <https://github.com/coq/coq/pull/19269>`_,
    by Lucas Donati and Andrej Dudenhefner and Pierre Rousselin).

- in `Zdiv.v`

  + lemma :g:`Z.mod_id_iff` generalizes :g:`Z.mod_small`.
    (`#19752 <https://github.com/coq/coq/pull/19752>`_,
    by Andres Erbsen).

  + lemmas :g:`Z.mod_opp_mod_opp`, :g:`Z.mod_mod_opp_r`,
    :g:`Z.mod_opp_r_mod`, :g:`Z.mod_mod_abs_r`, :g:`Z.mod_abs_r_mod`
    combining :g:`Z.modulo` with :g:`Z.opp` or :g:`Z.abs`
    (`#19752 <https://github.com/coq/coq/pull/19752>`_,
    by Andres Erbsen).

  + Lemmas :g:`cong_iff_0` and :g:`cong_iff_ex` can be used to reduce
    congruence equalities to equations where only one side is headed
    by :g:`Z.modulo`.
    (`#19752 <https://github.com/coq/coq/pull/19752>`_,
    by Andres Erbsen).

  + Lemmas :g:`Z.gcd_mod_l` and :g:`Z.gcd_mod_r` generalize
    :g:`Z.gcd_mod`.
    (`#19752 <https://github.com/coq/coq/pull/19752>`_,
    by Andres Erbsen).

  + Lemma :g:`Z.mod_mod_divide` generalizes :g:`Zmod_mod`.
    (`#19752 <https://github.com/coq/coq/pull/19752>`_,
    by Andres Erbsen).

  + Lemma :g:`Z.mod_pow_l` allows pushing modulo inside exponentiation
    (`#19752 <https://github.com/coq/coq/pull/19752>`_,
    by Andres Erbsen).

- file `Zdiv_facts.v`
  (`#19752 <https://github.com/coq/coq/pull/19752>`_,
  by Andres Erbsen).

- in `Zdiv_facts.v`

  + lemmas :g:`Z.diveq_iff` and :g:`Z.mod_diveq_iff` that further
    genralize the same concept as :g:`Z.mod_small` to known quotients
    other than 0.
    (`#19752 <https://github.com/coq/coq/pull/19752>`_,
    by Andres Erbsen).

  + lemmas :g:`Z.eq_mod_opp` and :g:`Z.eq_mod_abs`
    (`#19752 <https://github.com/coq/coq/pull/19752>`_,
    by Andres Erbsen).

- in `Znat.v`

  + lemmas :g:`N2Z.inj_lxor`, :g:`N2Z.inj_land`, :g:`N2Z.inj_lor`,
    :g:`N2Z.inj_ldiff`, :g:`N2Z.inj_shiftl`, and :g:`N2Z.inj_shiftr`
    relating bitwise operations on :g:`N` to those on :g:`Z`
    (`#19750 <https://github.com/coq/coq/pull/19750>`_,
    by Andres Erbsen).

Deprecated
^^^^^^^^^^

- modules :g:`ZArith_Base` and :g:`Ztac`,
  use :g:`ZArith` (or :g:`BinInt`) or :g:`Lia` instead
  (`#19801 <https://github.com/coq/coq/pull/19801>`_,
  by Andres Erbsen).

- in `Zbool.v`

  + definition :g:`Zeq_bool`, use :g:`Z.eqb` instead.
    (`#19801 <https://github.com/coq/coq/pull/19801>`_,
    by Andres Erbsen).

Previous versions
-----------------

The standard library historically used to be distributed with Coq,
please look in Coq own changelog for details about older changes.
