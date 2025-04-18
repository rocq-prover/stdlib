(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Definition of the predicate [isZ] with minimum dependencies.
    It is used byb [Rify] and is recognised by [lra].*)

From Stdlib Require Import Raxioms RIneq.

Definition isZ (r:R) := exists z:Z, IZR z = r.

Register isZ as micromega.isZ.

Definition isZ' (r:R) := IZR (up r - 1) = r.

Lemma isZ_eq : forall r, isZ r <-> isZ' r.
Proof.
  unfold isZ,isZ'.
  split ; intros.
  - destruct H. subst.
    destruct (archimed (IZR x)).
    apply Rgt_lt  in H.
    apply lt_IZR in H.
    rewrite <- minus_IZR in H0.
    apply le_IZR in H0.
    apply f_equal.
    (* proof over Z *)
    symmetry.
    apply Z.le_antisymm.
    apply Zorder.Zlt_succ_le.
    now ring_simplify.
    apply Zorder.Zle_minus_le_0 in H0.
    apply Zorder.Zle_0_minus_le.
    now replace (1 - (up (IZR x) - x))%Z with  (x - (up (IZR x) - 1))%Z in H0 by ring.
  - exists (up r - 1)%Z.
    congruence.
Qed.

Lemma isZ_dec : forall r, isZ r \/ ~ isZ r.
Proof.
  intros.
  rewrite isZ_eq.
  unfold isZ'.
  apply Req_dec.
Qed.


Definition isZb (r:R) := if Req_dec_T r (IZR (up r - 1)) then true else false.

Lemma isZ_isZb : forall r, isZ r <-> isZb r = true.
Proof.
  intros.
  rewrite isZ_eq.
  unfold isZ',isZb.
  split ; intros.
  - destruct (Req_dec_T r (IZR (up r - 1))).
    reflexivity.
    congruence.
  - destruct (Req_dec_T r (IZR (up r - 1))) ; try discriminate.
    congruence.
Qed.

Lemma isZb_IZR : forall x, isZb (IZR x) = true.
Proof.
  intros.
  rewrite <- isZ_isZb.
  exists x. reflexivity.
Qed.
