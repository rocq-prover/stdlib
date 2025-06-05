(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Functions on finite domains *)

(** Main result : for functions [f:A->A] with finite [A],
    f injective <-> f bijective <-> f surjective. *)

From Stdlib Require Import List ListDec.
Set Implicit Arguments.

(** General definitions *)

Definition Injective {A B} (f : A->B) :=
 forall x y, f x = f y -> x = y.

Definition Surjective {A B} (f : A->B) :=
 forall y, exists x, f x = y.

Definition Bijective {A B} (f : A->B) :=
 exists g:B->A, (forall x, g (f x) = x) /\ (forall y, f (g y) = y).

(** Finiteness is defined here via exhaustive list enumeration *)

Definition Full {A:Type} (l:list A) := forall a:A, In a l.
Definition Finite (A:Type) := exists (l:list A), Full l.

(** In many of the following proofs, it will be convenient to have
    list enumerations without duplicates. As soon as we have
    decidability of equality (in Prop), this is equivalent
    to the previous notion (s. lemma Finite_dec). *)

Definition Listing {A:Type} (l:list A) := NoDup l /\ Full l.
Definition Finite' (A:Type) := exists (l:list A), Listing l.

Lemma Listing_decidable_eq {A:Type} (l:list A): Listing l -> decidable_eq A.
Proof.
  intros (Hnodup & Hfull) a a'.
  now apply (NoDup_list_decidable Hnodup).
Qed.

Lemma Finite_dec {A:Type}: Finite A /\ decidable_eq A <-> Finite' A.
Proof.
  split.
  - intros ((l, Hfull) & Hdec).
    destruct (uniquify Hdec l) as (l' & H_nodup & H_inc).
    exists l'. split; trivial.
    intros a. apply H_inc. apply Hfull.
  - intros (l & Hlist).
    apply Listing_decidable_eq in Hlist as Heqdec.
    destruct Hlist as (Hnodup & Hfull).
    split; [ exists l | ]; assumption.
Qed.

(* Finite_alt is a weaker version of Finite_dec and has been deprecated.  *)
Lemma Finite_alt_deprecated A (d:decidable_eq A) : Finite A <-> Finite' A.
Proof.
 split.
 - intros F. now apply Finite_dec.
 - intros (l & _ & F). now exists l.
Qed.
#[deprecated(since="8.17", note="Use Finite_dec instead.")]
Notation Finite_alt := Finite_alt_deprecated.

(** Injections characterized in term of lists *)

Lemma Injective_map_NoDup A B (f:A->B) (l:list A) :
 Injective f -> NoDup l -> NoDup (map f l).
Proof.
 intros Ij. induction 1 as [|x l X N IH]; simpl; constructor; trivial.
 rewrite in_map_iff. intros (y & E & Y). apply Ij in E. now subst.
Qed.

Lemma Injective_map_NoDup_in A B (f:A->B) (l:list A) :
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
 pose proof @in_cons. pose proof @in_eq.
 intros Ij N; revert Ij; induction N; cbn [map]; constructor; auto.
 rewrite in_map_iff. intros (y & E & Y). apply Ij in E; auto; congruence.
Qed.

Lemma Injective_list_carac A B (d:decidable_eq A)(f:A->B) :
  Injective f <-> (forall l, NoDup l -> NoDup (map f l)).
Proof.
 split.
 - intros. now apply Injective_map_NoDup.
 - intros H x y E.
   destruct (d x y); trivial.
   assert (N : NoDup (x::y::nil)).
   { repeat constructor; simpl; intuition. }
   specialize (H _ N). simpl in H. rewrite E in H.
   inversion_clear H; simpl in *; intuition.
Qed.

Lemma Injective_carac A B (l:list A) : Listing l ->
   forall (f:A->B), Injective f <-> NoDup (map f l).
Proof.
 intros L f. split.
 - intros Ij. apply Injective_map_NoDup; trivial. apply L.
 - intros N x y E.
   assert (X : In x l) by apply L.
   assert (Y : In y l) by apply L.
   apply In_nth_error in X. destruct X as (i,X).
   apply In_nth_error in Y. destruct Y as (j,Y).
   assert (X' := map_nth_error f _ _ X).
   assert (Y' := map_nth_error f _ _ Y).
   assert (i = j).
   { rewrite NoDup_nth_error in N. apply N.
     - rewrite <- nth_error_Some. now rewrite X'.
     - rewrite X', Y'. now f_equal. }
   subst j. rewrite Y in X. now injection X.
Qed.

(** Surjection characterized in term of lists *)

Lemma Surjective_list_carac A B (f:A->B):
  Surjective f <-> (forall lB, exists lA, incl lB (map f lA)).
Proof.
 split.
 - intros Su lB.
   induction lB as [|b lB IH].
   + now exists nil.
   + destruct (Su b) as (a,E).
     destruct IH as (lA,IC).
     exists (a::lA). simpl. rewrite E.
     intros x [X|X]; simpl; intuition.
 - intros H y.
   destruct (H (y::nil)) as (lA,IC).
   assert (IN : In y (map f lA)) by (apply (IC y); now left).
   rewrite in_map_iff in IN. destruct IN as (x & E & _).
   now exists x.
Qed.

Lemma Surjective_carac A B : Finite B -> decidable_eq B ->
  forall f:A->B, Surjective f <-> (exists lA, Listing (map f lA)).
Proof.
 intros (lB,FB) d f. split.
 - rewrite Surjective_list_carac.
   intros Su. destruct (Su lB) as (lA,IC).
   destruct (uniquify_map d f lA) as (lA' & N & IC').
   exists lA'. split; trivial.
   intro x. apply IC', IC, FB.
 - intros (lA & N & FA) y.
   generalize (FA y). rewrite in_map_iff. intros (x & E & _).
   now exists x.
Qed.

(** Main result : *)

Lemma Endo_Injective_Surjective :
 forall A, Finite A -> decidable_eq A ->
  forall f:A->A, Injective f <-> Surjective f.
Proof.
 intros A F d f. rewrite (Surjective_carac F d). split.
 - assert (Finite' A) as (l, L) by (now apply Finite_dec); clear F.
   rewrite (Injective_carac L); intros.
   exists l; split; trivial.
   destruct L as (N,F).
   assert (I : incl l (map f l)).
   { apply NoDup_length_incl; trivial.
     - now rewrite length_map.
     - intros x _. apply F. }
   intros x. apply I, F.
 - clear F d. intros (l,L).
   assert (N : NoDup l). { apply (NoDup_map_inv f), L. }
   assert (I : incl (map f l) l).
   { apply NoDup_length_incl; trivial.
     - now rewrite length_map.
     - intros x _. apply L. }
   assert (L' : Listing l).
   { split; trivial.
     intro x. apply I, L. }
   apply (Injective_carac L'), L.
Qed.

(** An injective and surjective function is bijective.
    We need here stronger hypothesis : decidability of equality in Type. *)

Definition EqDec (A:Type) := forall x y:A, {x=y}+{x<>y}.

(** First, we show that a surjective f has an inverse function g such that
    f.g = id. *)

(* NB: instead of (Finite A), we could ask for (RecEnum A) with:
Definition RecEnum A := exists h:nat->A, surjective h.
*)

Lemma Finite_Empty_or_not A :
  Finite A -> (A->False) \/ exists a:A,True.
Proof.
 intros (l,F).
 destruct l as [|a l].
 - left; exact F.
 - right; now exists a.
Qed.

Lemma Surjective_inverse :
  forall A B, Finite A -> EqDec B ->
   forall f:A->B, Surjective f ->
    exists g:B->A, forall x, f (g x) = x.
Proof.
 intros A B F d f Su.
 destruct (Finite_Empty_or_not F) as [noA | (a,_)].
 - (* A is empty : g is obtained via False_rect *)
   assert (noB : B -> False). { intros y. now destruct (Su y). }
   exists (fun y => False_rect _ (noB y)).
   intro y. destruct (noB y).
 - (* A is inhabited by a : we use it in Option.get *)
   destruct F as (l,F).
   set (h := fun x k => if d (f k) x then true else false).
   set (get := fun o => match o with Some y => y | None => a end).
   exists (fun x => get (List.find (h x) l)).
   intros x.
   case_eq (find (h x) l); simpl; clear get; [intros y H|intros H].
   * apply find_some in H. destruct H as (_,H). unfold h in H.
     now destruct (d (f y) x) in H.
   * exfalso.
     destruct (Su x) as (y & Y).
     generalize (find_none _ l H y (F y)).
     unfold h. now destruct (d (f y) x).
Qed.

(** Same, with more knowledge on the inverse function: g.f = f.g = id *)

Lemma Injective_Surjective_Bijective :
 forall A B, Finite A -> EqDec B ->
  forall f:A->B, Injective f -> Surjective f -> Bijective f.
Proof.
 intros A B F d f Ij Su.
 destruct (Surjective_inverse F d Su) as (g, E).
 exists g. split; trivial.
 intros y. apply Ij. now rewrite E.
Qed.
