(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import BinInt Zdiv PreOmega Lia.
Local Open Scope Z_scope.

Module Z.

Lemma diveq_iff c a b :
  (b = 0 /\ c = 0 \/ c*b <= a < c*b + b \/ c*b + b < a <= c*b) <-> a/b = c.
Proof.
  destruct (Z.eqb_spec b 0); [subst; rewrite Z.div_0_r; intuition lia|].
  rewrite <-(Z.sub_move_0_r (_/_)),  <-(Z.add_opp_r (_/_)).
  rewrite <-Z.div_add, Z.div_small_iff; lia.
Qed.

Lemma mod_diveq_iff c a b :
  (b = 0 \/ c*b <= a < c*b + b \/ c*b + b < a <= c*b) <-> a mod b = a-b*c.
Proof.
  destruct (Z.eqb_spec b 0); [subst; rewrite Z.mod_0_r; intuition lia|].
  rewrite Z.mod_eq by trivial; pose proof diveq_iff c a b; nia.
Qed.

(* Usage: rewrite (mod_diveq (-1)) by lia *)
Definition mod_diveq c a b := proj1 (mod_diveq_iff c a b).

Definition diveq c a b := proj1 (diveq_iff c a b).

Lemma eq_mod_opp m x y : x mod -m = y mod -m <-> x mod m = y mod m.
Proof.
  intros.
  case (Z.eq_dec (x mod m) 0), (Z.eq_dec (y mod m) 0) as [];
    repeat rewrite ?Z_mod_zero_opp_r, ?Z_mod_nz_opp_r in * by lia.
  all : (intuition try trivial); Z.div_mod_to_equations; lia.
Qed.

Lemma eq_mod_abs m x y : x mod (Z.abs m) = y mod (Z.abs m) <-> x mod m = y mod m.
Proof.
  case (Z.abs_eq_or_opp m) as [->| ->].
  - reflexivity.
  - apply eq_mod_opp.
Qed.
End Z.
