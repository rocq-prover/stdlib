From Stdlib Require Import PeanoNat List Lia.
#[local] Set Warnings "-stdlib-vector".
From Stdlib.Compat Require Import Fin92.

#[universes(template)]
Inductive vec A : nat -> Type :=
| nil : vec _ 0
| cons (h : A) (n : nat) (tl : vec _ n) : vec _ (S n).
Arguments nil {_}.
Arguments cons {_} _ {_} _.
Notation t := vec (only parsing).

Section UniformElementType.
Context {A : Type}.

Fixpoint to_list {n} (v : vec A n) {struct v} : list A :=
  match v with
  | nil => List.nil
  | cons a v => List.cons a (to_list v)
  end.

Fixpoint of_list (l : list A) {struct l} : vec A (length l) :=
  match l with
  | List.nil => nil
  | List.cons h tail => cons h (of_list tail)
  end.

Definition cast {m} (v: t A m) {n} : m = n -> t A n :=
  match Nat.eq_dec m n with
  | left Heq => fun _ => eq_rect m _ v n Heq
  | right Hneq => fun Heq => False_rect _ (Hneq Heq)
  end.

Definition tl {n} (v : vec A (S n)) : vec A n := let 'cons _ v := v in v.

Definition hd {n} (v : vec A (S n)) : A := let 'cons a _ := v in a.

Definition hd_error {n} (v : vec A n) : option A :=
  match v with
  | nil => None
  | cons a v => Some a
  end.

Fixpoint snoc {n} (v:t A n) (a : A) {struct v} : t A (S n) :=
  match v with
  | nil => cons a nil
  | cons h t => cons h (snoc t a)
  end.

Fixpoint last {n} (v : vec A (S n)) {struct v} : A :=
  let '@cons _ a n v := v in
  match n return vec _ n -> _ with
  | O => fun _ => a
  | S _ => last
  end v.

Fixpoint app {n} (v : vec A n) {p} (w : vec A p) {struct v} : vec A (n+p) :=
  match v with
  | nil => w
  | cons a v => cons a (app v w)
  end.

Section WithA.
Context (a : A).
Fixpoint repeat n {struct n} : vec A n :=
  match n with
  | O => nil
  | S n => cons a (repeat n)
  end.
End WithA.

Fixpoint firstn {n} (v : vec A n) {struct v} : forall i, vec A (Nat.min n i) :=
  match v with
  | nil => fun _ => nil
  | cons a v => fun i =>
      match i with
      | O => nil
      | S i => cons a (firstn v i)
      end
  end.

Succeed
Fixpoint skipn (i : nat) {n} (v : vec A n) {struct i} : vec A (Nat.sub n i) :=
  match i with
  | O => cast v (eq_sym (Nat.sub_0_r n))
  | S i =>
      match v with
      | nil => nil
      | cons a v => skipn i v
      end
  end.

Fixpoint skipn {n} (v : vec A n) i {struct v} : vec A (Nat.sub n i) :=
  match v with
  | nil => match i with (O|_) => nil end
  | (cons a v') as v =>
      match i with
      | O => v
      | S i => skipn v' i
      end
  end.

Succeed
Fixpoint get {n : nat} (v : vec A n) (i : nat) {struct v} :=
  match v with
  | nil => None
  | cons a v =>
    match i with
    | O => Some a
    | S i => get v i
    end
  end.

Definition get {n} (v : vec A n) i := hd_error (skipn v i).

Fixpoint put {n : nat} (v : vec A n) (i : nat) (a : A) {struct v} :=
  match v with
  | nil => nil
  | cons b v =>
    match i with
    | O => cons a v
    | S i => cons b (put v i a)
    end
  end.

Section WithI.
Context (i : nat).
Definition lastn {n} (v : vec A n) : vec A (Nat.min n i).
(*
refine
  match Nat.eq_dec n (Nat.min n i) with
  | left Heq => eq_rect _ _ v _ Heq
  | right Hneq =>
    match v in vec _ n return _ -> vec _ (Nat.min n _) with
    | nil => fun _ => nil
    | @cons _ a n' v => fun _ => cast (@lastn _ v) _
    end Hneq
  end.
 *)
refine (cast (skipn v (n-i)) _).
abstract lia.
Defined.
End WithI.

Fixpoint unappl {i n} {struct i} : forall (v : vec A (i+n)), vec A i :=
  match i with
  | O => fun v => nil
  | S i => fun v => cons (hd v) (unappl (tl v))
  end.

Fixpoint unappr {i n} {struct i} : forall (v : vec A (i+n)), vec A n :=
  match i with
  | O => fun v => v
  | S i => fun v => unappr (tl v)
  end.

Fixpoint unapp (l : nat) {r : nat} : t A (l + r) -> t A l * t A r :=
  match l with
  | 0 => fun v => (nil, v)
  | S l' => fun v =>
    let (v1, v2) := unapp l' (tl v) in
    (cons (hd v) v1, v2)
  end.

Lemma length_to_list n (v : t A n) : length (to_list v) = n.
Proof. induction v; cbn [length to_list]; auto. Qed.

Local Definition rev_append {n p} (v : vec A n) (w : vec A p) : vec A (n + p).
  refine (cast (of_list (List.rev_append (to_list v) (to_list w))) _).
Proof.
  abstract (rewrite rev_append_rev, length_app, length_rev, 2 length_to_list; trivial).
Defined.

Definition rev {n} (v : vec A n) : vec A n.
  refine (cast (of_list (List.rev (to_list v))) _).
Proof. abstract (rewrite length_rev, length_to_list; trivial). Defined.
End UniformElementType.
Coercion to_list : t >-> list.
Arguments length_to_list [A] n v.

Section Map.
Context {A} {B} (f : A -> B).
Fixpoint map {n} (v:t A n) : t B n :=
  match v with
  | nil => nil
  | cons a v' => cons (f a) (map v')
  end.
End Map.

Section Map2.
Context {A B C} (f : A -> B -> C).
Fixpoint map2 {n} (v : vec A n) {struct v} : vec B n -> vec C n :=
  match v with
  | nil => fun _ => nil
  | cons a v => fun w => cons (f a (hd w)) (map2 v (tl w))
  end.
End Map2.

Section FoldLeft.
Context {A B : Type} (f:B->A->B).
Fixpoint fold_left (b : B) {n} (v : t A n) : B :=
  match v with
  | nil => b
  | cons a v => fold_left (f b a) v
  end.
End FoldLeft.

Section FoldRight.
Context {A B : Type} (f : A->B->B).
Fixpoint fold_right {n} (v : t A n) (b:B) {struct v} : B :=
  match v with
  | nil => b
  | cons a v => f a (fold_right v b)
  end.
End FoldRight.


Module Import VectorNotations.
Declare Scope vector_scope.
Delimit Scope vector_scope with vector.
Notation "[ ]" := nil (format "[ ]") : vector_scope.
Notation "h :: t" := (cons h t) (at level 60, right associativity)
  : vector_scope.
Notation "[ x ]" := (x :: nil) : vector_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : vector_scope.
Infix "++" := app : vector_scope.
Open Scope vector_scope.
End VectorNotations.


Section Forall.
Context {A} (P: A -> Prop).
Inductive Forall : forall {n} (v : vec A n), Prop :=
| Forall_nil : Forall nil
| Forall_cons {n} x (v : vec A n) (_ : P x) (_ : Forall v) : Forall (cons x v).
End Forall.

Section Exists.
Context {A} (P: A -> Prop).
Inductive Exists : forall {n}, vec A n -> Prop :=
| Exists_cons_hd {n} x v (_ : P x) : @Exists (S n) (cons x v)
| Exists_cons_tl {n} x v (_ : Exists v) : @Exists (S n) (cons x v).
End Exists.

Section In.
Context {A} (a : A).
Inductive In : forall {n}, vec A n -> Prop :=
| In_cons_hd {n} v : @In (S n) (cons a v)
| In_cons_tl {n} x v (_ : In v) : @In (S n) (cons x v).
End In.

Section Forall2.
Context {A B} (P:A->B->Prop).
Inductive Forall2 : forall {n}, vec A n -> vec B n -> Prop :=
| Forall2_nil : @Forall2 0 nil nil
| Forall2_cons {n} x1 x2 v1 v2 (_ : P x1 x2) (_ : Forall2 v1 v2)
  : @Forall2 (S n) (cons x1 v1) (cons x2 v2).
End Forall2.

Section Exists2.
Context {A B} (P : A->B->Prop).
Inductive Exists2 : forall {n}, vec A n -> vec B n -> Prop :=
| Exists2_cons_hd {n} x1 x2 v1 v2 (_ :  P x1 x2) : @Exists2 (S n) (x1::v1) (x2::v2)
| Exists2_cons_tl {n} x1 x2 v1 v2 (_ : Exists2 v1 v2) : @Exists2 (S n) (x1::v1) (x2::v2).
End Exists2.


Lemma inj_0 [A] (v : vec A 0) : v = nil.
Proof. exact (let 'nil := v in eq_refl). Qed.
 
Lemma inj_S [A n] (v : vec A (S n)) : v = cons (hd v) (tl v).
Proof. exact (let 'cons _ _ := v in eq_refl). Qed.

Lemma to_list_inj [A n] (v w : t A n) : to_list v = to_list w -> v = w.
Proof.
  induction n; cbn [to_list].
  { rewrite (inj_0 v), (inj_0 w); trivial. }
  { rewrite (inj_S v), (inj_S w); inversion 1; f_equal; eauto. }
Qed.

Lemma to_list_inj_iff [A n] (v w : t A n) : to_list v = to_list w <-> v = w.
Proof. split; try apply to_list_inj; congruence. Qed.

Lemma to_list_inj_dep [A m] (v : t A m) [n] (w : t A n) :
  to_list v = to_list w -> existT _ _ v = existT _ _ w.
Proof.
  intros H; specialize (f_equal (@length _) H); rewrite 2 length_to_list.
  destruct 1; auto using f_equal, to_list_inj.
Qed.

Lemma to_list_eq_rect [A m n] (p : m = n) v : to_list (eq_rect m (vec A) v n p) = to_list v.
Proof. case p; trivial. Qed.

Lemma to_list_cast [A m n] (p : m = n) (v : vec A m) : to_list (cast v p) = to_list v.
Proof. cbv[cast]. case Nat.eq_dec; intros; [apply to_list_eq_rect|contradiction]. Qed.


Lemma to_list_nil A : to_list (@nil A) = List.nil.
Proof. trivial. Qed.

Lemma to_list_cons [A n] a (v : t A n) : to_list (cons a v) = List.cons a v.
Proof. trivial. Qed.

Lemma to_list_of_list [A] (l : list A) : to_list (of_list l) = l.
Proof. induction l; cbn [to_list of_list]; congruence. Qed.

Lemma hd_to_list [A n] (d : A) (v : t A (S n)) : List.hd d v = hd v.
Proof. rewrite (inj_S v); trivial. Qed.

Lemma to_list_tl [A n] (v : t A (S n)) : to_list (tl v) = List.tl v.
Proof. rewrite (inj_S v); trivial. Qed.

Lemma last_to_list [A n] (d : A) (v : t A (S n)) : List.last v d = last v.
Proof.
  rewrite (inj_S v) in *.
  generalize (hd v); generalize (tl v); clear v; induction v; trivial.
  set (h::v) as hv; cbn [List.last to_list last]; subst hv. rewrite IHv. auto.
Qed.

Lemma to_list_repeat [A n] (a : A) : to_list (repeat a n) = List.repeat a n.
Proof. induction n; cbn [to_list repeat List.repeat]; auto using f_equal2. Qed.

Lemma to_list_app [A n p] (v : vec A n) (w : vec A p) : to_list (app v w) = List.app v w.
Proof. induction v; cbn [to_list app List.app]; rewrite ?IHv; trivial. Qed.

Lemma to_list_firstn [A n] (v : t A n) i : to_list (firstn v i) = List.firstn i v.
Proof. revert i; induction v, i; cbn [to_list firstn List.firstn]; congruence. Qed.

Lemma to_list_rev_append [A n p] (v : vec A n) (w : vec A p) :
  to_list (rev_append v w) = List.app (List.rev v) w.
Proof.
  cbv [rev_append]. rewrite to_list_cast, rev_append_rev, !to_list_of_list; trivial.
Qed.

Lemma to_list_rev [A n] (v : vec A n) : to_list (rev v) = List.rev v.
Proof. cbv [rev]. rewrite to_list_cast, to_list_of_list; trivial. Qed.

Lemma to_list_In A a n (v : t A n): In a v <-> List.In a (to_list v).
Proof.
  split.
  { induction 1; [left|right]; auto. }
  { induction v; inversion 1; subst; auto using In_cons_tl, In_cons_hd. }
Qed.

Lemma to_list_map [A B n] (f : A -> B) (v : vec A n) : to_list (map f v) = List.map f v.
Proof. induction v; cbn [to_list map List.map]; auto using f_equal. Qed.

Lemma to_list_map2 [A B C n] (f : A -> B -> C) (v : vec A n) (w : vec B n) :
  to_list (map2 f v w) = List.map (uncurry f) (List.combine v w).
Proof.
  induction v; [|rewrite (inj_S w)];
    cbn [to_list map2 List.map List.combine]; auto using f_equal.
Qed.

Lemma to_list_snoc [A n] (v : vec A n) a : to_list (snoc v a) = List.app v (List.cons a List.nil).
Proof. induction v; cbn; auto using f_equal. Qed.


(** * [app] *)

Lemma app_assoc_dep [A n m l] (a : vec A n) (b : vec A m) (c : vec A l) :
  existT _ _ (app a (app b c)) = existT _ _ (app (app a b) c).
Proof.
  apply to_list_inj_dep.
  induction a; cbn [app to_list]; auto using f_equal2.
Qed.

Lemma app_assoc [A n m l] (a : vec A n) (b : vec A m) (c : vec A l) :
  app a (app b c) = cast (app (app a b) c) (eq_sym (Nat.add_assoc _ _ _)).
Proof.
  pose proof app_assoc_dep a b c as E; symmetry in E; inversion_sigma.
  apply to_list_inj; rewrite <-E2, to_list_eq_rect, to_list_cast; trivial.
Qed.

Lemma sym_app_assoc [A n m l] (a : vec A n) (b : vec A m) (c : vec A l) :
  app (app a b) c = cast (app a (app b c)) (Nat.add_assoc _ _ _).
Proof.
  pose proof app_assoc_dep a b c as E; inversion_sigma.
  apply to_list_inj; rewrite <-E2, to_list_eq_rect, to_list_cast; trivial.
Qed.

Lemma app_repeat_repeat [A] (a : A) n m : app (repeat a n) (repeat a m) = repeat a (n + m).
Proof. induction n; cbn [app repeat Nat.add]; auto using f_equal. Qed.

(** * [rev] *)

Lemma rev_nil A : rev nil = nil :> vec A _.
Proof. trivial. Qed.

Lemma rev_cons [A n] a (v : vec A n) : rev (cons a v) = snoc (rev v) a.
Proof. erewrite <-to_list_inj_iff, to_list_snoc, 2 to_list_rev, to_list_cons, List.rev_cons; trivial. Qed.

Lemma rev_snoc [A n] (v : vec A n) a : rev (snoc v a) = cons a (rev v).
Proof. erewrite <-to_list_inj_iff, to_list_cons, 2 to_list_rev, to_list_snoc, List.rev_unit; trivial. Qed.

Lemma rev_rev [A n] (v : vec A n) : rev (rev v) = v.
Proof. apply to_list_inj; rewrite 2 to_list_rev, List.rev_involutive; trivial. Qed.

Lemma rev_map [A B] (f : A -> B) [n] (v : t A n) : rev (map f v) = map f (rev v).
Proof. apply to_list_inj; rewrite to_list_map, 2 to_list_rev, List.map_rev, to_list_map. trivial. Qed.

Lemma map_rev [A B] (f : A -> B) [n] (v : t A n) : map f (rev v) = rev (map f v).
Proof. apply to_list_inj; rewrite to_list_map, 2 to_list_rev, List.map_rev, to_list_map. trivial. Qed.


(** * [map] *)

Lemma map_nil [A B] (f : A -> B) : map f nil = nil.
Proof. trivial. Qed.

Lemma map_cons [A B] (f : A -> B) (a : A) [n] (v : vec A n) :
  map f (cons a v) = cons (f a) (map f v).
Proof. trivial. Qed.

Lemma map_map [A B C] (f : A -> B) (g : B -> C) [n] (v : vec A n) :
  map g (map f v) = map (fun x => g (f x)) v.
Proof. apply to_list_inj; rewrite 3 to_list_map, List.map_map; trivial. Qed.

Lemma map_ext_in [A B] (f g:A->B) [n] (v : t A n)
  (H : forall a, In a v -> f a = g a) : map f v = map g v.
Proof.  setoid_rewrite to_list_In in H; erewrite <-to_list_inj_iff, !to_list_map, List.map_ext_in; trivial. Qed.

Lemma map_ext [A B] (f g:A->B) [n] (v : t A n)
  (H : forall a, f a = g a) : map f v = map g v.
Proof. erewrite <-to_list_inj_iff, !to_list_map, List.map_ext; trivial. Qed.

Lemma map_app [A B] (f : A -> B) [n m] (v: t A n) (w: t A m) :
  map f (v ++ w) = map f v ++ map f w.
Proof. erewrite <-to_list_inj_iff, to_list_app, 3 to_list_map, to_list_app, List.map_app; trivial. Qed.

Lemma map_snoc [A B] (f : A -> B) [n] (v : vec A n) a :
  map f (snoc v a) = snoc (map f v) (f a).
Proof. induction v; cbn [map snoc]; auto using f_equal. Qed.


(** * [fold_right] *)

Lemma fold_right_snoc [A B] f (a : A) (b : B) n (v : vec A n) :
  fold_right f (snoc v a) b = fold_right f v (f a b).
Proof. induction v; cbn [snoc fold_right]; rewrite ?IHv; trivial. Qed.

Lemma fold_right_rev [A B] (f : A -> B -> B) [n] (v : vec A n) b :
  fold_right f (rev v) b = fold_left (fun x y => f y x) b v.
Proof.
  revert b; induction v; intros; rewrite ?rev_nil, ?rev_cons, ?fold_right_snoc; trivial.
Qed.


(** * [cast] *)

Lemma cast_nil [A] p : cast nil p = nil :> vec A 0.
Proof. trivial. Qed.

Lemma cast_cons [A m] a (v : vec A m) [n] p :
  cast (cons a v) p = cons a (cast v (Nat.succ_inj _ _ p)) :> vec A (S n).
Proof. apply to_list_inj; repeat rewrite ?to_list_cast, ?to_list_cons; trivial. Qed.

Lemma cast_refl [A n] (v : vec A n) p : cast v p = v.
Proof. apply to_list_inj; repeat rewrite ?to_list_cast; trivial. Qed.

Lemma cast_ext [A m] (v : vec A m) [n] p q : cast v p = cast v q :> vec A n.
Proof. apply to_list_inj; repeat rewrite ?to_list_cast; trivial. Qed.


(** * [put] *)

Lemma put_alt_subproof : forall x x0 : nat, Nat.min x x0 + (x - x0) = x.
Proof. lia. Qed.

Lemma put_alt [A n] (v : vec A n) (i : nat) (a : A) :
  put v i a = cast (app (firstn v i) (match skipn v i with nil => nil | cons _ v => cons a v end)) (put_alt_subproof n i).
Proof.
  revert i; induction v, i; cbn [put firstn app skipn Nat.min Nat.sub Nat.add];
    rewrite ?cast_refl, ?cast_cons, ?IHv; auto using f_equal, cast_ext.
Qed.
