(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Export RelationPairs SetoidList Orders EqualitiesFacts.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Specialization of results about lists modulo. *)

Module OrderedTypeLists (O:OrderedType).

#[local] Notation In:=(InA O.eq).
#[local] Notation Inf:=(lelistA O.lt).
#[local] Notation Sort:=(sort O.lt).
#[local] Notation NoDup:=(NoDupA O.eq).

Lemma In_eq : forall l x y, eq x y -> In x l -> In y l.
Proof. intros. rewrite <- H; auto. Qed.

Lemma ListIn_In : forall l x, List.In x l -> In x l.
Proof. exact (In_InA O.eq_equiv). Qed.

Lemma Inf_lt : forall l x y, O.lt x y -> Inf y l -> Inf x l.
Proof. exact (InfA_ltA O.lt_strorder). Qed.

Lemma Inf_eq : forall l x y, O.eq x y -> Inf y l -> Inf x l.
Proof. exact (InfA_eqA O.eq_equiv O.lt_compat). Qed.

Lemma Sort_Inf_In : forall l x a, Sort l -> Inf a l -> In x l -> O.lt a x.
Proof. exact (SortA_InfA_InA O.eq_equiv O.lt_strorder O.lt_compat). Qed.

Lemma ListIn_Inf : forall l x, (forall y, List.In y l -> O.lt x y) -> Inf x l.
Proof. exact (@In_InfA O.t O.lt). Qed.

Lemma In_Inf : forall l x, (forall y, In y l -> O.lt x y) -> Inf x l.
Proof. exact (InA_InfA O.eq_equiv (ltA:=O.lt)). Qed.

Lemma Inf_alt :
 forall l x, Sort l -> (Inf x l <-> (forall y, In y l -> O.lt x y)).
Proof. exact (InfA_alt O.eq_equiv O.lt_strorder O.lt_compat). Qed.

Lemma Sort_NoDup : forall l, Sort l -> NoDup l.
Proof. exact (SortA_NoDupA O.eq_equiv O.lt_strorder O.lt_compat) . Qed.

#[global]
Hint Resolve ListIn_In Sort_NoDup Inf_lt : core.
#[global]
Hint Immediate In_eq Inf_lt : core.

End OrderedTypeLists.


(** * Results about keys and data as manipulated in the future MMaps. *)

Module KeyOrderedType(O:OrderedType).
 Include KeyDecidableType(O). (* provides eqk, eqke *)

 #[local] Notation key:=O.t.
 #[local] Open Scope signature_scope.

 Definition ltk {elt} : relation (key*elt) := O.lt @@1.

 #[global]
 Hint Unfold ltk : core.

 (* ltk is a strict order *)

#[global]
 Instance ltk_strorder {elt} : StrictOrder (@ltk elt) := _.

#[global]
 Instance ltk_compat {elt} : Proper (eqk==>eqk==>iff) (@ltk elt).
 Proof. unfold eqk, ltk; auto with *. Qed.

#[global]
 Instance ltk_compat' {elt} : Proper (eqke==>eqke==>iff) (@ltk elt).
 Proof. eapply subrelation_proper; eauto with *. Qed.

 (* Additional facts *)

#[global]
 Instance pair_compat {elt} : Proper (O.eq==>Logic.eq==>eqke) (@pair key elt).
 Proof. apply pair_compat. Qed.

 Section Elt.
  Variable elt : Type.
  Implicit Type p q : key*elt.
  Implicit Type l m : list (key*elt).

  Lemma ltk_not_eqk p q : ltk p q -> ~ eqk p q.
  Proof.
  intros LT EQ; rewrite EQ in LT.
  elim (StrictOrder_Irreflexive _ LT).
  Qed.

  Lemma ltk_not_eqke p q : ltk p q -> ~eqke p q.
  Proof.
  intros LT EQ; rewrite EQ in LT.
  elim (StrictOrder_Irreflexive _ LT).
  Qed.

  Notation Sort := (sort ltk).
  Notation Inf := (lelistA ltk).

  Lemma Inf_eq l x x' : eqk x x' -> Inf x' l -> Inf x l.
  Proof. now intros <-. Qed.

  Lemma Inf_lt l x x' : ltk x x' -> Inf x' l -> Inf x l.
  Proof. apply InfA_ltA; auto with *. Qed.

  #[local]
  Hint Immediate Inf_eq : core.
  #[local]
  Hint Resolve Inf_lt : core.

  Lemma Sort_Inf_In l p q : Sort l -> Inf q l -> InA eqk p l -> ltk q p.
  Proof. apply SortA_InfA_InA; auto with *. Qed.

  Lemma Sort_Inf_NotIn l k e : Sort l -> Inf (k,e) l ->  ~In k l.
  Proof.
    intros; red; intros.
    destruct H1 as [e' H2].
    elim (@ltk_not_eqk (k,e) (k,e')).
    - eapply Sort_Inf_In; eauto.
    - repeat red; reflexivity.
  Qed.

  Lemma Sort_NoDupA l : Sort l -> NoDupA eqk l.
  Proof. apply SortA_NoDupA; auto with *. Qed.

  Lemma Sort_In_cons_1 l p q : Sort (p::l) -> InA eqk q l -> ltk p q.
  Proof.
   intros; invlist sort; eapply Sort_Inf_In; eauto.
  Qed.

  Lemma Sort_In_cons_2 l p q : Sort (p::l) -> InA eqk q (p::l) ->
      ltk p q \/ eqk p q.
  Proof.
    intros; invlist InA; auto with relations.
    left; apply Sort_In_cons_1 with l; auto with relations.
  Qed.

  Lemma Sort_In_cons_3 x l k e :
    Sort ((k,e)::l) -> In x l -> ~O.eq x k.
  Proof.
    intros; invlist sort; red; intros.
    eapply Sort_Inf_NotIn; eauto using In_eq.
  Qed.

 End Elt.

 #[global]
 Hint Resolve ltk_not_eqk ltk_not_eqke : core.
 #[global]
 Hint Immediate Inf_eq : core.
 #[global]
 Hint Resolve Inf_lt : core.
 #[global]
 Hint Resolve Sort_Inf_NotIn : core.

End KeyOrderedType.
