(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Export List.
From Stdlib Require Export Sorted.
From Stdlib Require Export Setoid Basics Morphisms.
Set Implicit Arguments.
Unset Strict Implicit.
(* Set Universe Polymorphism. *)
(** * Logical relations over lists with respect to a setoid equality
      or ordering. *)

(** This can be seen as a complement of predicate [lelistA] and [sort]
    found in [Sorting]. *)

Section Type_with_equality.
Variable A : Type.
Variable eqA : A -> A -> Prop.

(** Being in a list modulo an equality relation over type [A]. *)

Inductive InA (x : A) : list A -> Prop :=
  | InA_cons_hd : forall y l, eqA x y -> InA x (y :: l)
  | InA_cons_tl : forall y l, InA x l -> InA x (y :: l).

#[local]
Hint Constructors InA : core.

(** TODO: it would be nice to have a generic definition instead
    of the previous one. Having [InA = Exists eqA] raises too
    many compatibility issues. For now, we only state the equivalence: *)

Lemma InA_altdef : forall x l, InA x l <-> Exists (eqA x) l.
Proof. split; induction 1; auto. Qed.

Lemma InA_cons : forall x y l, InA x (y::l) <-> eqA x y \/ InA x l.
Proof.
 intuition. invlist InA; auto.
Qed.

Lemma InA_nil : forall x, InA x nil <-> False.
Proof.
 intuition. invlist InA.
Qed.

(** An alternative definition of [InA]. *)

Lemma InA_alt : forall x l, InA x l <-> exists y, eqA x y /\ In y l.
Proof.
 intros; rewrite InA_altdef, Exists_exists; firstorder.
Qed.

(** A list without redundancy modulo the equality over [A]. *)

Inductive NoDupA : list A -> Prop :=
  | NoDupA_nil : NoDupA nil
  | NoDupA_cons : forall x l, ~ InA x l -> NoDupA l -> NoDupA (x::l).

#[local]
Hint Constructors NoDupA : core.

(** An alternative definition of [NoDupA] based on [ForallOrdPairs] *)

Lemma NoDupA_altdef : forall l,
 NoDupA l <-> ForallOrdPairs (complement eqA) l.
Proof.
 split; induction 1 as [|a l H rest]; constructor; auto.
 - rewrite Forall_forall. intros b Hb.
   intro Eq; elim H. rewrite InA_alt. exists b; auto.
 - rewrite InA_alt; intros (a' & Haa' & Ha').
   rewrite Forall_forall in H. exact (H a' Ha' Haa').
Qed.


(** lists with same elements modulo [eqA] *)

Definition inclA l l' := forall x, InA x l -> InA x l'.
Definition equivlistA l l' := forall x, InA x l <-> InA x l'.

Lemma incl_nil l : inclA nil l.
Proof. intros a H. inversion H. Qed.
#[local]
Hint Resolve incl_nil : list.

(** lists with same elements modulo [eqA] at the same place *)

Inductive eqlistA : list A -> list A -> Prop :=
  | eqlistA_nil : eqlistA nil nil
  | eqlistA_cons : forall x x' l l',
      eqA x x' -> eqlistA l l' -> eqlistA (x::l) (x'::l').

#[local]
Hint Constructors eqlistA : core.

(** We could also have written [eqlistA = Forall2 eqA]. *)

Lemma eqlistA_altdef : forall l l', eqlistA l l' <-> Forall2 eqA l l'.
Proof. split; induction 1; auto. Qed.

(** Results concerning lists modulo [eqA] *)

Hypothesis eqA_equiv : Equivalence eqA.
Definition eqarefl := (@Equivalence_Reflexive _ _ eqA_equiv).
Definition eqatrans := (@Equivalence_Transitive _ _ eqA_equiv).
Definition eqasym := (@Equivalence_Symmetric _ _ eqA_equiv).

#[local]
Hint Resolve eqarefl eqatrans : core.
#[local]
Hint Immediate eqasym : core.

Ltac inv := invlist InA; invlist sort; invlist lelistA; invlist NoDupA.

(** First, the two notions [equivlistA] and [eqlistA] are indeed equivlances *)

#[global] Instance equivlist_equiv : Equivalence equivlistA.
Proof.
 firstorder.
Qed.

#[global] Instance eqlistA_equiv : Equivalence eqlistA.
Proof.
 constructor; red.
 - intros x; induction x; auto.
 - induction 1; auto.
 - intros x y z H; revert z; induction H; auto.
   inversion 1; subst; auto. invlist eqlistA; eauto with *.
Qed.
(** Moreover, [eqlistA] implies [equivlistA]. A reverse result
    will be proved later for sorted list without duplicates. *)

#[global] Instance eqlistA_equivlistA : subrelation eqlistA equivlistA.
Proof.
  intros x x' H. induction H as [|? ? ? ? H ? IHeqlistA].
  - intuition auto with relations.
  - red; intros x0.
    rewrite 2 InA_cons.
    rewrite (IHeqlistA x0), H; intuition.
Qed.

(** InA is compatible with eqA (for its first arg) and with
    equivlistA (and hence eqlistA) for its second arg *)

#[global] Instance InA_compat : Proper (eqA==>equivlistA==>iff) InA.
Proof.
 intros x x' Hxx' l l' Hll'. rewrite (Hll' x).
 rewrite 2 InA_alt; firstorder.
Qed.

(** For compatibility, an immediate consequence of [InA_compat] *)

Lemma InA_eqA : forall l x y, eqA x y -> InA x l -> InA y l.
Proof.
 intros l x y H H'. rewrite <- H. auto.
Qed.
#[local]
Hint Immediate InA_eqA : core.

Lemma In_InA : forall l x, In x l -> InA x l.
Proof.
 intros l; induction l; simpl; intuition.
 subst; auto.
Qed.
#[local]
Hint Resolve In_InA : core.

Lemma InA_split : forall l x, InA x l ->
 exists l1 y l2, eqA x y /\ l = l1++y::l2.
Proof.
intros l; induction l as [|a l IHl]; intros x H; inv.
- exists (@nil A); exists a; exists l; auto.
- match goal with H' : InA x l |- _ => rename H' into H0 end.
  destruct (IHl x H0) as (l1,(y,(l2,(H1,H2)))).
  exists (a::l1); exists y; exists l2; auto.
  split; simpl; f_equal; auto.
Qed.

Lemma InA_app : forall l1 l2 x,
 InA x (l1 ++ l2) -> InA x l1 \/ InA x l2.
Proof.
 intros l1; induction l1 as [|a l1 IHl1]; simpl in *; intuition.
 inv; auto.
 match goal with H0' : InA _ (l1 ++ _) |- _ => rename H0' into H0 end.
 elim (IHl1 _ _ H0); auto.
Qed.

Lemma InA_app_iff : forall l1 l2 x,
 InA x (l1 ++ l2) <-> InA x l1 \/ InA x l2.
Proof.
 split.
 - apply InA_app.
 - destruct 1 as [H|H]; generalize H; do 2 rewrite InA_alt.
   + destruct 1 as (y,(H1,H2)); exists y; split; auto.
     apply in_or_app; auto.
   + destruct 1 as (y,(H1,H2)); exists y; split; auto.
     apply in_or_app; auto.
Qed.

Lemma InA_rev : forall p m,
 InA p (rev m) <-> InA p m.
Proof.
 intros; do 2 rewrite InA_alt.
 split; intros (y,H); exists y; intuition.
 - rewrite In_rev; auto.
 - rewrite <- In_rev; auto.
Qed.

(** Some more facts about InA *)

Lemma InA_singleton x y : InA x (y::nil) <-> eqA x y.
Proof.
 rewrite InA_cons, InA_nil; tauto.
Qed.

Lemma InA_double_head x y l :
 InA x (y :: y :: l) <-> InA x (y :: l).
Proof.
 rewrite !InA_cons; tauto.
Qed.

Lemma InA_permute_heads x y z l :
 InA x (y :: z :: l) <-> InA x (z :: y :: l).
Proof.
 rewrite !InA_cons; tauto.
Qed.

Lemma InA_app_idem x l : InA x (l ++ l) <-> InA x l.
Proof.
 rewrite InA_app_iff; tauto.
Qed.

Section NoDupA.

Lemma NoDupA_app : forall l l', NoDupA l -> NoDupA l' ->
  (forall x, InA x l -> InA x l' -> False) ->
  NoDupA (l++l').
Proof.
intros l; induction l as [|a l IHl]; simpl; auto; intros l' H H0 H1.
inv.
constructor.
- rewrite InA_alt; intros (y,(H4,H5)).
  destruct (in_app_or _ _ _ H5).
  + match goal with H2' : ~ InA a l |- _ => rename H2' into H2 end.
    elim H2.
    rewrite InA_alt.
    exists y; auto.
  + apply (H1 a).
    * auto.
    * rewrite InA_alt.
      exists y; auto.
- apply IHl; auto.
  intros x ? ?.
  apply (H1 x); auto.
Qed.

Lemma NoDupA_rev : forall l, NoDupA l -> NoDupA (rev l).
Proof.
intros l; induction l.
- simpl; auto.
- simpl; intros.
  inv.
  apply NoDupA_app; auto.
  + constructor; auto.
    intro; inv.
  + intros x.
    rewrite InA_alt.
    intros (x1,(H2,H3)).
    intro; inv.
    match goal with H0 : ~ InA _ _ |- _ => destruct H0 end.
    match goal with H4 : eqA x ?x' |- InA ?x' _ => rewrite <- H4, H2 end.
    apply In_InA.
    rewrite In_rev; auto.
Qed.

Lemma NoDupA_split : forall l l' x, NoDupA (l++x::l') -> NoDupA (l++l').
Proof.
 intros l; induction l; simpl in *; intros; inv; auto.
 constructor; eauto.
 match goal with H0 : ~ InA _ _ |- _ => contradict H0 end.
 rewrite InA_app_iff in *.
 rewrite InA_cons.
 intuition.
Qed.

Lemma NoDupA_swap : forall l l' x, NoDupA (l++x::l') -> NoDupA (x::l++l').
Proof.
 intros l; induction l as [|a l IHl]; simpl in *; intros l' x H; inv; auto.
 constructor; eauto.
 - match goal with H1 : NoDupA (l ++ x :: l') |- _ => assert (H2:=IHl _ _ H1) end.
   inv.
   rewrite InA_cons.
   red; destruct 1.
   + match goal with H0 : ~ InA a (l ++ x :: l') |- _ => apply H0 end.
     rewrite InA_app_iff in *; rewrite InA_cons; auto.
   + auto.
 - constructor.
   + match goal with H0 : ~ InA a (l ++ x :: l') |- _ => contradict H0 end.
     rewrite InA_app_iff in *; rewrite InA_cons; intuition.
   + eapply NoDupA_split; eauto.
Qed.

Lemma NoDupA_singleton x : NoDupA (x::nil).
Proof.
 repeat constructor. inversion 1.
Qed.

End NoDupA.

Section EquivlistA.

#[global] Instance equivlistA_cons_proper:
 Proper (eqA ==> equivlistA ==> equivlistA) (@cons A).
Proof.
 intros ? ? E1 ? ? E2 ?; now rewrite !InA_cons, E1, E2.
Qed.

#[global] Instance equivlistA_app_proper:
 Proper (equivlistA ==> equivlistA ==> equivlistA) (@app A).
Proof.
 intros ? ? E1 ? ? E2 ?. now rewrite !InA_app_iff, E1, E2.
Qed.

Lemma equivlistA_cons_nil x l : ~ equivlistA (x :: l) nil.
Proof.
 intros E. now eapply InA_nil, E, InA_cons_hd.
Qed.

Lemma equivlistA_nil_eq l : equivlistA l nil -> l = nil.
Proof.
 destruct l.
 - trivial.
 - intros H. now apply equivlistA_cons_nil in H.
Qed.

Lemma equivlistA_double_head x l : equivlistA (x :: x :: l) (x :: l).
Proof.
 intro. apply InA_double_head.
Qed.

Lemma equivlistA_permute_heads x y l :
 equivlistA (x :: y :: l) (y :: x :: l).
Proof.
 intro. apply InA_permute_heads.
Qed.

Lemma equivlistA_app_idem l : equivlistA (l ++ l) l.
Proof.
 intro. apply InA_app_idem.
Qed.

Lemma equivlistA_NoDupA_split l l1 l2 x y : eqA x y ->
 NoDupA (x::l) -> NoDupA (l1++y::l2) ->
 equivlistA (x::l) (l1++y::l2) -> equivlistA l (l1++l2).
Proof.
 intros H H0 H1 H2; intro a.
 generalize (H2 a).
 rewrite !InA_app_iff, !InA_cons.
 inv.
 assert (SW:=NoDupA_swap H1). inv.
 rewrite InA_app_iff in *.
 split; intros.
 - match goal with H3 : ~ InA x l |- _ =>
                     assert (~eqA a x) by (contradict H3; rewrite <- H3; auto)
   end.
   assert (~eqA a y) by (rewrite <- H; auto).
   tauto.
 - assert (OR : eqA a x \/ InA a l) by intuition.
   destruct OR as [EQN|INA]; auto.
   match goal with H0 : ~ (InA y l1 \/ InA y l2) |- _ => elim H0 end.
   rewrite <-H,<-EQN; auto.
Qed.

End EquivlistA.

Section Fold.

Variable B:Type.
Variable eqB:B->B->Prop.
Variable st:Equivalence eqB.
Variable f:A->B->B.
Variable i:B.
Variable Comp:Proper (eqA==>eqB==>eqB) f.

Lemma fold_right_eqlistA :
   forall s s', eqlistA s s' ->
   eqB (fold_right f i s) (fold_right f i s').
Proof.
induction 1; simpl; auto with relations.
apply Comp; auto.
Qed.

(** Fold with restricted [transpose] hypothesis. *)

Section Fold_With_Restriction.
Variable R : A -> A -> Prop.
Hypothesis R_sym : Symmetric R.
Hypothesis R_compat : Proper (eqA==>eqA==>iff) R.


(*

(** [ForallOrdPairs R] is compatible with [equivlistA] over the
    lists without duplicates, as long as the relation [R]
    is symmetric and compatible with [eqA]. To prove this fact,
    we use an auxiliary notion: "forall distinct pairs, ...".
*)

Definition ForallNeqPairs :=
 ForallPairs (fun a b => ~eqA a b -> R a b).

(** [ForallOrdPairs] and [ForallNeqPairs] are related, but not completely
    equivalent. For proving one implication, we need to know that the
    list has no duplicated elements... *)

Lemma ForallNeqPairs_ForallOrdPairs : forall l, NoDupA l ->
 ForallNeqPairs l -> ForallOrdPairs R l.
Proof.
 induction l; auto.
 constructor. inv.
 rewrite Forall_forall; intros b Hb.
 apply H0; simpl; auto.
 contradict H1; rewrite H1; auto.
 apply IHl.
 inv; auto.
 intros b c Hb Hc Hneq.
 apply H0; simpl; auto.
Qed.

(** ... and for proving the other implication, we need to be able
   to reverse relation [R]. *)

Lemma ForallOrdPairs_ForallNeqPairs : forall l,
 ForallOrdPairs R l -> ForallNeqPairs l.
Proof.
 intros l Hl x y Hx Hy N.
 destruct (ForallOrdPairs_In Hl x y Hx Hy) as [H|[H|H]].
 subst; elim N; auto.
 assumption.
 apply R_sym; assumption.
Qed.

*)

(** Compatibility of [ForallOrdPairs] with respect to [inclA]. *)

Lemma ForallOrdPairs_inclA : forall l l',
 NoDupA l' -> inclA l' l -> ForallOrdPairs R l -> ForallOrdPairs R l'.
Proof.
intros l l'. induction l' as [|x l' IH].
- constructor.
- intros ND Incl FOP. apply FOP_cons; inv; unfold inclA in *; auto.
  rewrite Forall_forall; intros y Hy.
  assert (Ix : InA x (x::l')) by (rewrite InA_cons; auto).
  apply Incl in Ix. rewrite InA_alt in Ix. destruct Ix as (x' & Hxx' & Hx').
  assert (Iy : InA y (x::l')) by (apply In_InA; simpl; auto).
  apply Incl in Iy. rewrite InA_alt in Iy. destruct Iy as (y' & Hyy' & Hy').
  rewrite Hxx', Hyy'.
  destruct (ForallOrdPairs_In FOP x' y' Hx' Hy') as [E|[?|?]]; auto.
  absurd (InA x l'); auto. rewrite Hxx', E, <- Hyy'; auto.
Qed.


(** Two-argument functions that allow to reorder their arguments. *)
Definition transpose (f : A -> B -> B) :=
  forall (x y : A) (z : B), eqB (f x (f y z)) (f y (f x z)).

(** A version of transpose with restriction on where it should hold *)
Definition transpose_restr (R : A -> A -> Prop)(f : A -> B -> B) :=
  forall (x y : A) (z : B), R x y -> eqB (f x (f y z)) (f y (f x z)).

Variable TraR :transpose_restr R f.

Lemma fold_right_commutes_restr :
  forall s1 s2 x, ForallOrdPairs R (s1++x::s2) ->
  eqB (fold_right f i (s1++x::s2)) (f x (fold_right f i (s1++s2))).
Proof.
intros s1; induction s1 as [|a s1 IHs1]; simpl; auto; intros s2 x H.
- reflexivity.
- transitivity (f a (f x (fold_right f i (s1++s2)))).
  + apply Comp; auto.
    apply IHs1.
    invlist ForallOrdPairs; auto.
  + apply TraR.
    invlist ForallOrdPairs; auto.
    match goal with H0 : Forall (R a) (s1 ++ x :: s2) |- R a x =>
                      rewrite Forall_forall in H0; apply H0
    end.
    apply in_or_app; simpl; auto.
Qed.

Lemma fold_right_equivlistA_restr :
  forall s s', NoDupA s -> NoDupA s' -> ForallOrdPairs R s ->
  equivlistA s s' -> eqB (fold_right f i s) (fold_right f i s').
Proof.
 intros s; induction s as [|x l Hrec].
 - intros s'; destruct s' as [|a s']; simpl.
   + intros; reflexivity.
   + unfold equivlistA; intros H H0 H1 H2.
     destruct (H2 a).
     assert (InA a nil) by auto; inv.
 - intros s' N N' F E; simpl in *.
   assert (InA x s') as H by (rewrite <- (E x); auto).
   destruct (InA_split H) as (s1,(y,(s2,(H1,H2)))).
   subst s'.
   transitivity (f x (fold_right f i (s1++s2))).
   + apply Comp; auto.
     apply Hrec; auto.
     * inv; auto.
     * eapply NoDupA_split; eauto.
     * invlist ForallOrdPairs; auto.
     * eapply equivlistA_NoDupA_split; eauto.
   + transitivity (f y (fold_right f i (s1++s2))).
     * apply Comp; auto. reflexivity.
     * symmetry; apply fold_right_commutes_restr.
       apply ForallOrdPairs_inclA with (x::l); auto.
       red; intros; rewrite E; auto.
Qed.

Lemma fold_right_add_restr :
  forall s' s x, NoDupA s -> NoDupA s' -> ForallOrdPairs R s' -> ~ InA x s ->
  equivlistA s' (x::s) -> eqB (fold_right f i s') (f x (fold_right f i s)).
Proof.
 intros s' s x **; apply (@fold_right_equivlistA_restr s' (x::s)); auto.
Qed.

End Fold_With_Restriction.

(** we now state similar results, but without restriction on transpose. *)

Variable Tra :transpose f.

Lemma fold_right_commutes : forall s1 s2 x,
  eqB (fold_right f i (s1++x::s2)) (f x (fold_right f i (s1++s2))).
Proof.
intros s1; induction s1 as [|a s1 IHs1]; simpl; auto; intros s2 x.
- reflexivity.
- transitivity (f a (f x (fold_right f i (s1++s2)))); auto.
  apply Comp; auto.
Qed.

Lemma fold_right_equivlistA :
  forall s s', NoDupA s -> NoDupA s' ->
  equivlistA s s' -> eqB (fold_right f i s) (fold_right f i s').
Proof.
intros; apply (fold_right_equivlistA_restr (R:=fun _ _ => True));
 repeat red; auto.
apply ForallPairs_ForallOrdPairs; try red; auto.
Qed.

Lemma fold_right_add :
  forall s' s x, NoDupA s -> NoDupA s' -> ~ InA x s ->
  equivlistA s' (x::s) -> eqB (fold_right f i s') (f x (fold_right f i s)).
Proof.
 intros s' s x **; apply (@fold_right_equivlistA s' (x::s)); auto.
Qed.

End Fold.


Section Fold2.

Variable B:Type.
Variable eqB:B->B->Prop.
Variable st:Equivalence eqB.
Variable f:A->B->B.
Variable Comp:Proper (eqA==>eqB==>eqB) f.


Lemma fold_right_eqlistA2 :
  forall s s' (i j:B) (heqij: eqB i j) (heqss': eqlistA s s'),
  eqB (fold_right f i s) (fold_right f j s').
Proof.
  intros s.
  induction s as [|a s IHs];intros s' i j heqij heqss'.
  - inversion heqss'.
    subst.
    simpl.
    assumption.
  - inversion heqss'.
    subst.
    simpl.
    apply Comp.
    + assumption.
    + apply IHs;assumption.
Qed.

Section Fold2_With_Restriction.

Variable R : A -> A -> Prop.
Hypothesis R_sym : Symmetric R.
Hypothesis R_compat : Proper (eqA==>eqA==>iff) R.

(** Two-argument functions that allow to reorder their arguments. *)
Definition transpose2 (f : A -> B -> B) :=
  forall (x y : A) (z z': B), eqB z z' -> eqB (f x (f y z)) (f y (f x z')).

(** A version of transpose with restriction on where it should hold *)
Definition transpose_restr2 (R : A -> A -> Prop)(f : A -> B -> B) :=
  forall (x y : A) (z z': B), R x y -> eqB z z' -> eqB (f x (f y z)) (f y (f x z')).

Variable TraR :transpose_restr2 R f.

Lemma fold_right_commutes_restr2 :
  forall s1 s2 x (i j:B) (heqij: eqB i j), ForallOrdPairs R (s1++x::s2) ->
  eqB (fold_right f i (s1++x::s2)) (f x (fold_right f j (s1++s2))).
Proof.
intros s1; induction s1 as [|a s1 IHs1]; simpl; auto; intros s2 x i j heqij ?.
- apply Comp.
  + destruct eqA_equiv. apply Equivalence_Reflexive.
  + eapply fold_right_eqlistA2.
    * assumption.
    * reflexivity.
- transitivity (f a (f x (fold_right f j (s1++s2)))).
  + apply Comp; auto.
    eapply IHs1.
    * assumption.
    * invlist ForallOrdPairs; auto.
  + apply TraR.
    * invlist ForallOrdPairs; auto.
      match goal with H0 : Forall (R a) (s1 ++ x :: s2) |- _ =>
                        rewrite Forall_forall in H0; apply H0
      end.
      apply in_or_app; simpl; auto.
    * reflexivity.
Qed.

Lemma fold_right_equivlistA_restr2 :
  forall s s' i j,
    NoDupA s -> NoDupA s' -> ForallOrdPairs R s ->
    equivlistA s s' -> eqB i j ->
    eqB (fold_right f i s) (fold_right f j s').
Proof.
 intros s; induction s as [|x l Hrec].
 { intros s'; destruct s' as [|a s']; simpl.
   - intros. assumption.
   - unfold equivlistA; intros ? ? H H0 H1 H2 **.
     destruct (H2 a).
     assert (InA a nil) by auto; inv.
 }
 intros s' i j N N' F E eqij; simpl in *.
 assert (InA x s') as H by (rewrite <- (E x); auto).
 destruct (InA_split H) as (s1,(y,(s2,(H1,H2)))).
 subst s'.
 transitivity (f x (fold_right f j (s1++s2))).
 - apply Comp; auto.
   apply Hrec; auto.
   + inv; auto.
   + eapply NoDupA_split; eauto.
   + invlist ForallOrdPairs; auto.
   + eapply equivlistA_NoDupA_split; eauto.
 - transitivity (f y (fold_right f i (s1++s2))).
   + apply Comp; auto.
     symmetry.
     apply fold_right_eqlistA2.
     * assumption.
     * reflexivity.
   + symmetry.
     apply fold_right_commutes_restr2.
     * symmetry.
       assumption.
     * apply ForallOrdPairs_inclA with (x::l); auto.
       red; intros; rewrite E; auto.
Qed.

Lemma fold_right_add_restr2 :
  forall s' s i j x, NoDupA s -> NoDupA s' -> eqB i j -> ForallOrdPairs R s' -> ~ InA x s ->
  equivlistA s' (x::s) -> eqB (fold_right f i s') (f x (fold_right f j s)).
Proof.
 intros s' s i j x **; apply (@fold_right_equivlistA_restr2 s' (x::s) i j); auto.
Qed.

End Fold2_With_Restriction.

Variable Tra :transpose2 f.

Lemma fold_right_commutes2 : forall s1 s2 i x x',
  eqA x x' ->
  eqB (fold_right f i (s1++x::s2)) (f x' (fold_right f i (s1++s2))).
Proof.
  intros s1; induction s1 as [|a s1 IHs1];simpl;intros s2 i x x' H.
- apply Comp;auto.
  reflexivity.
- transitivity (f a (f x' (fold_right f i (s1++s2)))); auto.
  + apply Comp;auto.
  + apply Tra.
    reflexivity.
Qed.

Lemma fold_right_equivlistA2 :
  forall s s' i j, NoDupA s -> NoDupA s' -> eqB i j ->
  equivlistA s s' -> eqB (fold_right f i s) (fold_right f j s').
Proof.
red in Tra.
intros; apply (fold_right_equivlistA_restr2 (R:=fun _ _ => True));
repeat red; auto.
apply ForallPairs_ForallOrdPairs; try red; auto.
Qed.

Lemma fold_right_add2 :
  forall s' s i j x, NoDupA s -> NoDupA s' -> eqB i j -> ~ InA x s ->
  equivlistA s' (x::s) -> eqB (fold_right f i s') (f x (fold_right f j s)).
Proof.
 intros s' s i j x **.
 replace (f x (fold_right f j s)) with (fold_right f j (x::s)) by auto.
 eapply fold_right_equivlistA2;auto.
Qed.

End Fold2.

Section Remove.

Hypothesis eqA_dec : forall x y : A, {eqA x y}+{~(eqA x y)}.

Lemma InA_dec : forall x l, { InA x l } + { ~ InA x l }.
Proof.
intros x l; induction l as [|a l IHl].
- right; auto.
  intro; inv.
- destruct (eqA_dec x a).
  + left; auto.
  + destruct IHl.
    * left; auto.
    * right; intro; inv; contradiction.
Defined.

Fixpoint removeA (x : A) (l : list A) : list A :=
  match l with
    | nil => nil
    | y::tl => if (eqA_dec x y) then removeA x tl else y::(removeA x tl)
  end.

Lemma removeA_filter : forall x l,
  removeA x l = filter (fun y => if eqA_dec x y then false else true) l.
Proof.
intros x l; induction l as [|a l IHl]; simpl; auto.
destruct (eqA_dec x a); auto.
rewrite IHl; auto.
Qed.

Lemma removeA_InA : forall l x y, InA y (removeA x l) <-> InA y l /\ ~eqA x y.
Proof.
intros l; induction l as [|a l IHl]; simpl; auto.
- intros x y; split.
  + intro; inv.
  + destruct 1; inv.
- intros x y.
  destruct (eqA_dec x a) as [Heq|Hnot]; simpl; auto.
  + rewrite IHl; split; destruct 1; split; auto.
    inv; auto.
    match goal with H0 : ~ eqA x y |- _ => destruct H0 end; transitivity a; auto.
  + split.
    * intro; inv.
      -- split; auto.
         contradict Hnot.
         transitivity y; auto.
      -- match goal with H0 : InA y (removeA x l) |- _ =>
                           rewrite (IHl x y) in H0; destruct H0; auto
         end.
    * destruct 1; inv; auto.
      right; rewrite IHl; auto.
Qed.

Lemma removeA_NoDupA :
  forall s x, NoDupA s ->  NoDupA (removeA x s).
Proof.
intros s; induction s as [|a s IHs]; simpl; intros x ?.
- auto.
- inv.
  destruct (eqA_dec x a); simpl; auto.
  constructor; auto.
  rewrite removeA_InA.
  intuition.
Qed.

Lemma removeA_equivlistA : forall l l' x,
  ~InA x l -> equivlistA (x :: l) l' -> equivlistA l (removeA x l').
Proof.
unfold equivlistA; intros l l' x H H0 x0.
rewrite removeA_InA.
split; intros H1.
- rewrite <- H0; split; auto.
  contradict H.
  apply InA_eqA with x0; auto.
- rewrite <- (H0 x0) in H1.
  destruct H1.
  inv; auto.
  match goal with H2 : ~ eqA x x0 |- _ => elim H2; auto end.
Qed.

End Remove.



(** Results concerning lists modulo [eqA] and [ltA] *)

Variable ltA : A -> A -> Prop.
Hypothesis ltA_strorder : StrictOrder ltA.
Hypothesis ltA_compat : Proper (eqA==>eqA==>iff) ltA.

Let sotrans := (@StrictOrder_Transitive _ _ ltA_strorder).

#[local]
Hint Resolve sotrans : core.

Notation InfA:=(lelistA ltA).
Notation SortA:=(sort ltA).

#[local]
Hint Constructors lelistA sort : core.

Lemma InfA_ltA :
 forall l x y, ltA x y -> InfA y l -> InfA x l.
Proof.
 intros l; destruct l; constructor. inv; eauto.
Qed.

#[global] Instance InfA_compat : Proper (eqA==>eqlistA==>iff) InfA.
Proof using eqA_equiv ltA_compat. (* and not ltA_strorder *)
 intros x x' Hxx' l l' Hll'.
 inversion_clear Hll'.
 - intuition.
 - split; intro; inv; constructor.
   + match goal with H : eqA _ _ |- _ => rewrite <- Hxx', <- H; auto end.
   + match goal with H : eqA _ _ |- _ => rewrite Hxx', H; auto end.
Qed.

(** For compatibility, can be deduced from [InfA_compat] *)
Lemma InfA_eqA l x y : eqA x y -> InfA y l -> InfA x l.
Proof using eqA_equiv ltA_compat.
 intros H; now rewrite H.
Qed.
#[local]
Hint Immediate InfA_ltA InfA_eqA : core.

Lemma SortA_InfA_InA :
 forall l x a, SortA l -> InfA a l -> InA x l -> ltA a x.
Proof.
 intros l; induction l as [|a l IHl].
 - intros x a **. inv.
 - intros x a0 **. inv.
   + setoid_replace x with a; auto.
   + eauto.
Qed.

Lemma In_InfA :
 forall l x, (forall y, In y l -> ltA x y) -> InfA x l.
Proof.
 intros l; induction l; simpl; intros; constructor; auto.
Qed.

Lemma InA_InfA :
 forall l x, (forall y, InA y l -> ltA x y) -> InfA x l.
Proof.
 intros l; induction l; simpl; intros; constructor; auto.
Qed.

(* In fact, this may be used as an alternative definition for InfA: *)

Lemma InfA_alt :
 forall l x, SortA l -> (InfA x l <-> (forall y, InA y l -> ltA x y)).
Proof.
split.
- intros; eapply SortA_InfA_InA; eauto.
- apply InA_InfA.
Qed.

Lemma InfA_app : forall l1 l2 a, InfA a l1 -> InfA a l2 -> InfA a (l1++l2).
Proof.
 intros l1; induction l1; simpl; auto.
 intros; inv; auto.
Qed.

Lemma SortA_app :
 forall l1 l2, SortA l1 -> SortA l2 ->
 (forall x y, InA x l1 -> InA y l2 -> ltA x y) ->
 SortA (l1 ++ l2).
Proof.
 intros l1; induction l1; intros l2; simpl in *; intuition.
 inv.
 constructor; auto.
 apply InfA_app; auto.
 destruct l2; auto.
Qed.

Lemma SortA_NoDupA : forall l, SortA l -> NoDupA l.
Proof.
 intros l; induction l as [|x l' H]; auto.
 intros H0.
 inv.
 constructor; auto.
 intro.
 apply (StrictOrder_Irreflexive x).
 eapply SortA_InfA_InA; eauto.
Qed.


(** Some results about [eqlistA] *)

Section EqlistA.

Lemma eqlistA_length : forall l l', eqlistA l l' -> length l = length l'.
Proof.
induction 1; auto; simpl; congruence.
Qed.

#[global] Instance app_eqlistA_compat :
 Proper (eqlistA==>eqlistA==>eqlistA) (@app A).
Proof.
 repeat red; induction 1; simpl; auto.
Qed.

(** For compatibility, can be deduced from app_eqlistA_compat **)
Lemma eqlistA_app : forall l1 l1' l2 l2',
   eqlistA l1 l1' -> eqlistA l2 l2' -> eqlistA (l1++l2) (l1'++l2').
Proof.
intros l1 l1' l2 l2' H H'; rewrite H, H'; reflexivity.
Qed.

Lemma eqlistA_rev_app : forall l1 l1',
   eqlistA l1 l1' -> forall l2 l2', eqlistA l2 l2' ->
   eqlistA ((rev l1)++l2) ((rev l1')++l2').
Proof.
induction 1; auto.
simpl; intros.
do 2 rewrite <- app_assoc; simpl; auto.
Qed.

#[global] Instance rev_eqlistA_compat : Proper (eqlistA==>eqlistA) (@rev A).
Proof.
repeat red. intros x y ?.
rewrite <- (app_nil_r (rev x)), <- (app_nil_r (rev y)).
apply eqlistA_rev_app; auto.
Qed.

Lemma eqlistA_rev : forall l1 l1',
   eqlistA l1 l1' -> eqlistA (rev l1) (rev l1').
Proof.
apply rev_eqlistA_compat.
Qed.

Lemma SortA_equivlistA_eqlistA : forall l l',
   SortA l -> SortA l' -> equivlistA l l' -> eqlistA l l'.
Proof.
intros l; induction l as [|a l IHl]; intros l'; destruct l' as [|a0 l']; simpl; intros H H0 H1; auto.
- destruct (H1 a0); assert (InA a0 nil) by auto; inv.
- destruct (H1 a); assert (InA a nil) by auto; inv.
- inv.
  assert (forall y, InA y l -> ltA a y) by
    (intros; eapply (SortA_InfA_InA (l:=l)); eauto).
  assert (forall y, InA y l' -> ltA a0 y) by
    (intros; eapply (SortA_InfA_InA (l:=l')); eauto).
  do 2 match goal with H : InfA _ _ |- _ => clear H end.
  assert (eqA a a0).
  + destruct (H1 a).
    destruct (H1 a0).
    assert (InA a (a0::l')) by auto. inv; auto.
    assert (InA a0 (a::l)) by auto. inv; auto.
    elim (StrictOrder_Irreflexive a); eauto.
  + constructor; auto.
    apply IHl; auto.
    intros x; split; intros.
    * destruct (H1 x).
      assert (InA x (a0::l')) by auto. inv; auto.
      match goal with H3 : eqA a a0, H4 : InA x l, H9 : eqA x a0 |- InA x l' =>
                        rewrite H9,<-H3 in H4
      end.
      elim (StrictOrder_Irreflexive a); eauto.
    * destruct (H1 x).
      assert (InA x (a::l)) by auto. inv; auto.
      match goal with H3 : eqA a a0, H4 : InA x l', H9 : eqA x a |- InA x l =>
                        rewrite H9,H3 in H4
      end.
      elim (StrictOrder_Irreflexive a0); eauto.
Qed.

End EqlistA.

(** A few things about [filter] *)

Section Filter.

Lemma filter_sort : forall f l, SortA l -> SortA (List.filter f l).
Proof.
intros f l; induction l as [|a l IHl]; simpl; auto.
intros; inv; auto.
destruct (f a); auto.
constructor; auto.
apply In_InfA; auto.
intros y H.
rewrite filter_In in H; destruct H.
eapply SortA_InfA_InA; eauto.
Qed.
Arguments eq {A} x _.

Lemma filter_InA : forall f, Proper (eqA==>eq) f ->
 forall l x, InA x (List.filter f l) <-> InA x l /\ f x = true.
Proof.
(* Unset Mangle Names. *)
clear sotrans ltA ltA_strorder ltA_compat.
intros f H l x; do 2 rewrite InA_alt; intuition;
  match goal with Hex' : exists _, _ |- _ => rename Hex' into Hex end.
- destruct Hex as (y,(H0,H1)); rewrite filter_In in H1; exists y; intuition.
- destruct Hex as (y,(H0,H1)); rewrite filter_In in H1; intuition.
  rewrite (H _ _ H0); auto.
- destruct Hex as (y,(H0,H1)); exists y; rewrite filter_In; intuition.
  rewrite <- (H _ _ H0); auto.
Qed.

Lemma filter_split :
 forall f, (forall x y, f x = true -> f y = false -> ltA x y) ->
 forall l, SortA l -> l = filter f l ++ filter (fun x=>negb (f x)) l.
Proof.
intros f H l; induction l as [|a l IHl]; simpl; intros H0; auto.
inv.
match goal with H1' : SortA l, H2' : InfA a l |- _ => rename H1' into H1, H2' into H2 end.
rewrite IHl at 1; auto.
case_eq (f a); simpl; intros; auto.
assert (forall e, In e l -> f e = false) as H3. {
  intros e H3.
  assert (H4:=SortA_InfA_InA H1 H2 (In_InA H3)).
  case_eq (f e); simpl; intros; auto.
  elim (StrictOrder_Irreflexive e).
  transitivity a; auto.
}
replace (List.filter f l) with (@nil A); auto.
generalize H3; clear; induction l as [|a l IHl]; simpl; auto.
case_eq (f a); auto; intros H H3.
rewrite H3 in H; auto; try discriminate.
Qed.

End Filter.
End Type_with_equality.

#[global]
Hint Constructors InA eqlistA NoDupA sort lelistA : core.

Arguments equivlistA_cons_nil {A} eqA {eqA_equiv} x l _.
Arguments equivlistA_nil_eq {A} eqA {eqA_equiv} l _.

Section Find.

Variable A B : Type.
Variable eqA : A -> A -> Prop.
Hypothesis eqA_equiv : Equivalence eqA.
Hypothesis eqA_dec : forall x y : A, {eqA x y}+{~(eqA x y)}.

Fixpoint findA (f : A -> bool) (l:list (A*B)) : option B :=
 match l with
  | nil => None
  | (a,b)::l => if f a then Some b else findA f l
 end.

Lemma findA_NoDupA :
 forall l a b,
 NoDupA (fun p p' => eqA (fst p) (fst p')) l ->
 (InA (fun p p' => eqA (fst p) (fst p') /\ snd p = snd p') (a,b) l <->
  findA (fun a' => if eqA_dec a a' then true else false) l = Some b).
Proof.
set (eqk := fun p p' : A*B => eqA (fst p) (fst p')).
set (eqke := fun p p' : A*B => eqA (fst p) (fst p') /\ snd p = snd p').
intros l; induction l as [|a l IHl]; intros a0 b H; simpl.
- split; intros H0; try discriminate.
  invlist InA.
- destruct a as (a',b'); rename a0 into a.
  invlist NoDupA.
  split; intros.
  + invlist InA.
    * match goal with H2 : eqke (a, b) (a', b') |- _ => compute in H2; destruct H2 end.
      subst b'.
      destruct (eqA_dec a a'); intuition.
    * destruct (eqA_dec a a') as [HeqA|]; simpl.
      -- match goal with H0 : ~ InA eqk (a', b') l |- _ => contradict H0 end.
         match goal with H2 : InA eqke (a, b) l |- _ => revert HeqA H2; clear - eqA_equiv end.
         induction l.
         ++ intros; invlist InA.
         ++ intros; invlist InA; auto.
            match goal with |- InA eqk _ (?p :: _) => destruct p as [a0 b0] end.
            match goal with H : eqke (a, b) (a0, b0) |- _ => compute in H; destruct H end.
            subst b.
            left; auto.
            compute.
            transitivity a; auto. symmetry; auto.
      -- rewrite <- IHl; auto.
  + destruct (eqA_dec a a'); simpl in *.
    * left; split; simpl; congruence.
    * right. rewrite IHl; auto.
Qed.

End Find.

(** Compatibility aliases. [Proper] is rather to be used directly now.*)

Definition compat_bool {A} (eqA:A->A->Prop)(f:A->bool) :=
 Proper (eqA==>Logic.eq) f.

Definition compat_nat {A} (eqA:A->A->Prop)(f:A->nat) :=
 Proper (eqA==>Logic.eq) f.

Definition compat_P {A} (eqA:A->A->Prop)(P:A->Prop) :=
 Proper (eqA==>impl) P.

Definition compat_op {A B} (eqA:A->A->Prop)(eqB:B->B->Prop)(f:A->B->B) :=
 Proper (eqA==>eqB==>eqB) f.
