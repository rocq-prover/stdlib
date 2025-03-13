.. _changes:

--------------
Recent changes
--------------

.. ifconfig:: not is_a_released_version

   .. include:: ../unreleased.rst

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
