(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Attributes deprecated(since="9.1", note="Vector92 will replace Vector in Stdlib for Rocq 9.2. You can Require Import that file directly now.").
Local Set Warnings "-deprecated,-stdlib-vector".

(** Definitions of Vectors and functions to use them

   Initial Author: Pierre Boutillier
   Institution: PPS, INRIA 12/2010
*)

From Stdlib Require Import Compat.Fin92 Compat.Vector92 VectorFin.

From Stdlib Require Import Arith_base.
From Stdlib Require Vectors.Fin.
Import EqNotations.
Local Open Scope nat_scope.

Universe u.
#[deprecated(since="9.1", use=Vector92.vec)]
Notation t := Vector92.vec (only parsing).
#[deprecated(since="9.1", use=Vector92.nil)]
Notation nil := Vector92.nil (only parsing).
#[deprecated(since="9.1", use=Vector92.cons)]
Notation cons := Vector92.cons (only parsing).
#[deprecated(since="9.1", use=Vector92.vec_ind)]
Notation t_ind := Vector92.vec_ind (only parsing).
#[deprecated(since="9.1", use=Vector92.vec_rect)]
Notation t_rect := Vector92.vec_ind (only parsing).
#[deprecated(since="9.1", use=Vector92.vec_rec)]
Notation t_rec := Vector92.vec_ind (only parsing).
#[deprecated(since="9.1", use=Vector92.vec_sind)]
Notation t_sind := Vector92.vec_sind (only parsing).

Arguments nil : clear implicits.
Arguments cons : clear implicits.
Arguments t_ind : clear implicits.
Arguments t_rect : clear implicits.
Arguments t_rec : clear implicits.
Arguments t_sind : clear implicits.

Local Notation "[ ]" := (nil _) (format "[ ]").
Local Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

Section SCHEMES.

(** An induction scheme for non-empty vectors *)

#[deprecated(since="9.1", note="Use small inversions. Elaborator input: let '@cons _ a n' v' := v in ...")]
Definition rectS {A} (P:forall {n}, t A (S n) -> Type)
 (bas: forall a: A, P (a :: []))
 (rect: forall a {n} (v: t A (S n)), P v -> P (a :: v)) :=
 fix rectS_fix {n} (v: t A (S n)) : P v :=
 match v with
 |@cons _ a 0 v =>
   match v with
     |nil _ => bas a
     |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
   end
 |@cons _ a (S nn') v => rect a v (rectS_fix v)
 |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
 end.

(** A vector of length [0] is [nil] *)
#[deprecated(since="9.1", use=Vector92.inj_0)]
Definition case0 {A} (P:t A 0 -> Type) (H:P (nil A)) v:P v :=
match v with
  |[] => H
  |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
end.

(** A vector of length [S _] is [cons] *)
#[deprecated(since="9.1", use=Vector92.inj_S)]
Definition caseS {A} (P : forall {n}, t A (S n) -> Type)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v :=
match v with
  |h :: t => H h t
  |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
end.

#[deprecated(since="9.1", use=Vector92.inj_S)]
Definition caseS' {A} {n : nat} (v : t A (S n)) : forall (P : t A (S n) -> Type)
  (H : forall h t, P (h :: t)), P v :=
  match v with
  | h :: t => fun P H => H h t
  | _ => fun devil => False_rect (@IDProp) devil
  end.

#[deprecated(since="9.1", use=Vector92.inj_S)]
(** An induction scheme for 2 vectors of same length *)
Definition rect2 {A B} (P:forall {n}, t A n -> t B n -> Type)
  (bas : P [] []) (rect : forall {n v1 v2}, P v1 v2 ->
    forall a b, P (a :: v1) (b :: v2)) :=
  fix rect2_fix {n} (v1 : t A n) : forall v2 : t B n, P v1 v2 :=
  match v1 with
  | [] => fun v2 => case0 _ bas v2
  | @cons _ h1 n' t1 => fun v2 =>
    caseS' v2 (fun v2' => P (h1::t1) v2') (fun h2 t2 => rect (rect2_fix t1 t2) h1 h2)
  end.

End SCHEMES.

Section BASES.
(** The first element of a non empty vector *)
#[deprecated(since="9.1", use=Vector92.hd)]
Definition hd {A} := @caseS _ (fun n v => A) (fun h n t => h).
Global Arguments hd {A} {n} v.

#[deprecated(since="9.1", use=Vector92.hd)]
Lemma hd_92 [A n] v : @hd A n v = @Vector92.hd A n v.
Proof. rewrite (inj_S v); reflexivity. Qed.

(** The last element of an non empty vector *)
#[deprecated(since="9.1", use=Vector92.last)]
Definition last {A} := @rectS _ (fun _ _ => A) (fun a => a) (fun _ _ _ H => H).
Global Arguments last {A} {n} v.

#[deprecated(since="9.1", use=Vector92.last)]
Lemma last_92 [A] n v : @last A n v = @Vector92.last A n v.
Proof.
  rewrite (inj_S v); set (Vector92.hd v) as h; set (tl v) as t; clearbody h t; clear v.
  revert h; induction t; trivial; [].
  set (_ :: t) as v; cbn [last Vector92.last rectS]; cbv [v]; auto.
Qed.

(** Build a vector of n{^ th} [a] *)
#[deprecated(since="9.1", use=Vector92.repeat)]
Definition const {A} (a:A) := nat_rect _ [] (fun n x => cons _ a n x).

#[deprecated(since="9.1", use=Vector92.repeat)]
Lemma const_92 : @const = @repeat.
Proof. reflexivity. Qed.

(** The [p]{^ th} element of a vector of length [m].

Computational behavior of this function should be the same as
ocaml function. *)
#[deprecated(since="9.1", use=getFin)]
Definition nth {A} :=
  fix nth_fix {n : nat} (v : t A n) {struct v} : Fin.t n -> A :=
    match v with
    | nil _ => fun p => False_rect A (Fin.case0 _ p)
    | cons _ x m v' => fun p =>
      match p in (Fin.t m') return t A (pred m') -> A with
      | Fin.F1 => fun _ => x
      | Fin.FS p' => fun v' => nth_fix v' p'
      end v'
    end.

#[deprecated(since="9.1", use=getFin)]
Lemma nth_92 A n v i : @nth A n v i = @getFin A n v i.
Proof. induction i; trivial; try rewrite (inj_S v); cbn; trivial. Qed.

(** An equivalent definition of [nth]. *)
#[deprecated(since="9.1", use=getLt)]
Definition nth_order {A} {n} (v: t A n) {p} (H: p < n) :=
(nth v (Fin.of_nat_lt H)).

Lemma nth_order_92 [A n] v p H : @nth_order A n v p H = @getLt A n v p H.
Proof. cbv [nth_order getLt]. rewrite nth_92. f_equal.
(* Fin.of_nat_lt H = of_nat n p H *)
Admitted.

(** Put [a] at the p{^ th} place of [v] *)
#[deprecated(since="9.1", use=putFin)]
Fixpoint replace {A n} (v : t A n) (p: Fin.t n) (a : A) {struct p}: t A n :=
  match p with
  | @Fin.F1 k => fun v': t A (S k) => caseS' v' _ (fun h t => a :: t)
  | @Fin.FS k p' => fun v' : t A (S k) =>
    (caseS' v' (fun _ => t A (S k)) (fun h t => h :: (replace t p' a)))
  end v.

#[deprecated(since="9.1", use=putFin)]
Lemma replace_92 A n v i x : @replace A n v i x = @putFin A n v i x.
Proof. induction i; trivial; try rewrite (inj_S v); cbn; congruence. Qed.

(** Version of replace with [lt] *)
#[deprecated(since="9.1", use=putLt)]
Definition replace_order {A n} (v: t A n) {p} (H: p < n) :=
replace v (Fin.of_nat_lt H).

Lemma replace_order_92 [A n] v p H x : @replace_order A n v p H x = @putLt A n v p H x.
Proof. cbv [replace_order putLt]. rewrite replace_92. f_equal.
(* Fin.of_nat_lt H = of_nat n p H *)
Admitted.

(** Remove the first element of a non empty vector *)
#[deprecated(since="9.1", use=Vector92.tl)]
Definition tl {A} := @caseS _ (fun n v => t A n) (fun h n t => t).
Global Arguments tl {A} {n} v.

#[deprecated(since="9.1", use=Vector92.tl)]
Lemma tl_92 [A n] v : @tl A n v = @Vector92.tl A n v.
Proof. rewrite (inj_S v); reflexivity. Qed.

(** Destruct a non empty vector *)
#[deprecated(since="9.1", note="Use small inversions. Elaborator input: let '@cons _ a n' v' := v in ...")]
Definition uncons {A} {n : nat} (v : t A (S n)) : A * t A n := (hd v, tl v).

(** Remove last element of a non-empty vector *)
#[deprecated(since="9.1", note="If you would like stdlib to keep this definition, please open an issue.")]
Definition shiftout {A} := @rectS _ (fun n _ => t A n) (fun a => [])
  (fun h _ _ H => h :: H).
Global Arguments shiftout {A} {n} v.

#[deprecated(since="9.1", use=Vector92.snoc)]
(** Add an element at the end of a vector *)
Fixpoint shiftin {A} {n:nat} (a : A) (v:t A n) : t A (S n) :=
match v with
  |[] => a :: []
  |h :: t => h :: (shiftin a t)
end.

#[deprecated(since="9.1", use=Vector92.snoc)]
Lemma shiftin_92 [A n] x v : @shiftin A n x v = @Vector92.snoc A n v x.
Proof. induction v; cbn; congruence. Qed.

(** Copy last element of a vector *)
#[deprecated(since="9.1", note="If you would like stdlib to keep this definition, please open an issue.")]
Definition shiftrepeat {A} := @rectS _ (fun n _ => t A (S (S n)))
  (fun h =>  h :: h :: []) (fun h _ _ H => h :: H).
Global Arguments shiftrepeat {A} {n} v.

(** Take first [p] elements of a vector *)
#[deprecated(since="9.1", use=Vector92.firstn)]
Fixpoint take {A} {n} (p:nat) (le:p <= n) (v:t A n) : t A p :=
  match p as p return p <= n -> t A p with
  | 0 => fun _ => []
  | S p' => match v in t _ n return S p' <= n -> t A (S p') with
    | []=> fun le => False_rect _ (Nat.nle_succ_0 p' le)
    | x::xs => fun le => x::take p' (le_S_n p' _ le) xs
    end
  end le.

#[deprecated(since="9.1", use=Vector92.firstn)]
Lemma take_92_dep [A n] p le v : existT _ _ (@take A n p le v) = existT _ _ (@Vector92.firstn A n v p).
Proof.
  revert dependent p; induction v, p; cbn [Nat.min take firstn]; auto;
    [pose proof Nat.nle_succ_0 p; contradiction|intros].
  specialize (IHv _ (le_S_n p n le)); symmetry in IHv; inversion_sigma.
  rewrite <-IHv2; clear IHv2.
  apply to_list_inj_dep.
  rewrite 2 to_list_cons, to_list_eq_rect; trivial.
Qed.

#[deprecated(since="9.1", use=Vector92.firstn)]
Lemma take_92 [A n] p le v : @take A n p le v = cast (@Vector92.firstn A n v p) (Nat.min_r _ _ le).
Proof.
  pose proof eq_sym (take_92_dep p le v) as Hr; inversion_sigma.
  rewrite <-Hr2; clear Hr2.
  apply to_list_inj; rewrite to_list_eq_rect, to_list_cast; trivial.
Qed.

(** Remove [p] last elements of a vector *)
#[deprecated(since="9.1", use=Vector92.firstn, note="If you would like stdlib to keep this definition, please open an issue.")]
Lemma trunc : forall {A} {n} (p:nat), n > p -> t A n
  -> t A (n - p).
Proof.
  intros A n p; induction p as [| p f]; intros H v.
  - rewrite Nat.sub_0_r.
    exact v.

  - apply shiftout.

    rewrite <- Nat.sub_succ_l.
    + exact (f (Nat.lt_le_incl _ _ H) v).
    + exact (Nat.lt_le_incl _ _ H).
Defined.

(** Concatenation of two vectors *)
#[deprecated(since="9.1", use=Vector92.app)]
Fixpoint append {A}{n}{p} (v:t A n) (w:t A p):t A (n+p) :=
  match v with
  | [] => w
  | a :: v' => a :: (append v' w)
  end.

#[deprecated(since="9.1", use=Vector92.app)]
Lemma append_92 {A} l p v w : @append A l p v w = @Vector92.app A l v p w.
Proof. induction v; cbn; congruence. Qed.

#[deprecated(since="9.1")]
Infix "++" := append.

(** Split a vector into two parts *)
#[deprecated(since="9.1", use=Vector92.unapp)]
Fixpoint splitat {A} (l : nat) {r : nat} :
  t A (l + r) -> t A l * t A r :=
  match l with
  | 0 => fun v => ([], v)
  | S l' => fun v =>
    let (v1, v2) := splitat l' (tl v) in
    (hd v::v1, v2)
  end.

#[deprecated(since="9.1", use=Vector92.unapp)]
Lemma splitat_92 {A} l r v : @splitat A l r v = @Vector92.unapp A l r v.
Proof. induction l; cbn; rewrite <-?IHl, ?hd_92, ?tl_92; trivial. Qed.

(** Two definitions of the tail recursive function that appends two lists but
reverses the first one *)

#[deprecated(since="9.1", use=Vector92.rev_append, note="If you would like stdlib to keep this definition, please open an issue.")]
(** This one has the exact expected computational behavior *)
Fixpoint rev_append_tail {A n p} (v : t A n) (w: t A p)
  : t A (Nat.tail_add n p) :=
  match v with
  | [] => w
  | a :: v' => rev_append_tail v' (a :: w)
  end.

#[deprecated(since="9.1", use=Vector92.rev_append)]
Lemma rev_append_tail_92 [A n p] v w : existT _ _ (@rev_append_tail A n p v w) = existT _ _ (@Vector92.rev_append A n p v w).
Proof.
  revert dependent p; induction v; intros.
  { cbv [Vector92.rev_append];
    apply to_list_inj_dep;
    rewrite ?to_list_cast, ?to_list_of_list; cbn; rewrite ?IHv; trivial. }
  { cbn; rewrite IHv.
    apply to_list_inj_dep; cbv [Vector92.rev_append].
    rewrite ?to_list_cast, ?to_list_cons, ?to_list_of_list.
    rewrite !List.rev_append_rev; cbn; rewrite <-!List.app_assoc; trivial. }
Qed.

Import EqdepFacts.

(** This one has a better type *)
#[deprecated(since="9.1", use=Vector92.rev_append, note="If you would like stdlib to keep this definition, please open an issue.")]
Definition rev_append {A n p} (v: t A n) (w: t A p)
  :t A (n + p) :=
  rew (Nat.tail_add_spec n p) in (rev_append_tail v w).

#[deprecated(since="9.1", use=Vector92.rev_append)]
Lemma rev_append_92 [A n p] v w : @rev_append A n p v w = @Vector92.rev_append A n p v w.
Proof.
  apply to_list_inj. cbv [rev_append]. rewrite to_list_eq_rect.
  pose proof eq_sym (@rev_append_tail_92 A n p v w) as HH; inversion_sigma; rewrite <-HH2.
  rewrite to_list_eq_rect; trivial.
Qed.
(** rev [a₁ ; a₂ ; .. ; an] is [an ; a{n-1} ; .. ; a₁]

Caution : There is a lot of rewrite garbage in this definition *)
#[deprecated(since="9.1", use=Vector92.rev)]
Definition rev {A n} (v : t A n) : t A n :=
 rew <- (plus_n_O _) in (rev_append v []).

#[deprecated(since="9.1", use=Vector92.rev)]
Lemma rev_92 [A n] v : @rev A n v = @Vector92.rev A n v.
Proof.
  apply to_list_inj; cbv [rev eq_rect_r]; rewrite to_list_eq_rect.
  rewrite (@rev_append_92 A n 0 v (nil _)); trivial.
  rewrite to_list_rev_append, to_list_rev, List.app_nil_r; trivial.
Qed.

End BASES.
Local Notation "v [@ p ]" := (nth v p) (at level 1).

Section ITERATORS.
(** * Here are special non dependent useful instantiation of induction schemes *)

(** Uniform application on the arguments of the vector *)
#[deprecated(since="9.1", use=Vector92.map)]
Definition map {A} {B} (f : A -> B) : forall {n} (v:t A n), t B n :=
  fix map_fix {n} (v : t A n) : t B n := match v with
  | [] => []
  | a :: v' => (f a) :: (map_fix v')
  end.

#[deprecated(since="9.1", use=Vector92.map)]
Lemma map_92 : @map = @Vector92.map.
Proof. reflexivity. Qed.

(** map2 g [x1 .. xn] [y1 .. yn] = [(g x1 y1) .. (g xn yn)] *)
#[deprecated(since="9.1", use=Vector92.map2)]
Definition map2 {A B C} (g:A -> B -> C) :
  forall (n : nat), t A n -> t B n -> t C n :=
@rect2 _ _ (fun n _ _ => t C n) (nil C) (fun _ _ _ H a b => (g a b) :: H).
Global Arguments map2 {A B C} g {n} v1 v2.

#[deprecated(since="9.1", use=Vector92.map2)]
Lemma map2_92 {A B C} f n v w : @map2 A B C f n v w = @Vector92.map2 A B C f n v w.
Proof.
  induction v; rewrite (inj_0 w) || rewrite (inj_S w); cbn; f_equal; trivial.
Qed.

(** fold_left f b [x1 .. xn] = f .. (f (f b x1) x2) .. xn *)
#[deprecated(since="9.1", use=Vector92.fold_left)]
Definition fold_left {A B:Type} (f:B->A->B): forall (b:B) {n} (v:t A n), B :=
  fix fold_left_fix (b:B) {n} (v : t A n) : B := match v with
    | [] => b
    | a :: w => (fold_left_fix (f b a) w)
  end.

#[deprecated(since="9.1", use=Vector92.fold_right)]
Lemma fold_left_92 : @fold_left = @Vector92.fold_left.
Proof. reflexivity. Qed.

(** fold_right f [x1 .. xn] b = f x1 (f x2 .. (f xn b) .. ) *)
#[deprecated(since="9.1", use=Vector92.fold_right)]
Definition fold_right {A B : Type} (f : A->B->B) :=
  fix fold_right_fix {n} (v : t A n) (b:B)
  {struct v} : B :=
  match v with
    | [] => b
    | a :: w => f a (fold_right_fix w b)
  end.

#[deprecated(since="9.1", use=Vector92.fold_right)]
Lemma fold_right_92 : @fold_right = @Vector92.fold_right.
Proof. reflexivity. Qed.

(** fold_right2 g c [x1 .. xn] [y1 .. yn] = g x1 y1 (g x2 y2 .. (g xn yn c) .. )
    c is before the vectors to be compliant with "refolding". *)
#[deprecated(since="9.1", note="Use Vector92.fold_right and Vector92.map2. Please open an issue if you would like stdlib to keep this definition.")]
Definition fold_right2 {A B C} (g:A -> B -> C -> C) (c: C) :=
@rect2 _ _ (fun _ _ _ => C) c (fun _ _ _ H a b => g a b H).


(** fold_left2 f b [x1 .. xn] [y1 .. yn] = g .. (g (g a x1 y1) x2 y2) .. xn yn *)
#[deprecated(since="9.1", note="Use Vector92.fold_left and Vector92.map2. Please open an issue if you would like stdlib to keep this definition.")]
Definition fold_left2 {A B C: Type} (f : A -> B -> C -> A) :=
fix fold_left2_fix (a : A) {n} (v : t B n) : t C n -> A :=
match v in t _ n0 return t C n0 -> A with
  |[] => fun w => case0 (fun _ => A) a w
  |@cons _ vh vn vt => fun w =>
    caseS' w (fun _ => A) (fun wh wt => fold_left2_fix (f a vh wh) vt wt)
end.

End ITERATORS.

#[deprecated(since="9.1", use=Vector92.Forall)]
Notation Forall := Vector92.Forall (only parsing).

#[deprecated(since="9.1", use=Vector92.Exists)]
Notation Exists := Vector92.Exists (only parsing).

#[deprecated(since="9.1", use=Vector92.Forall2)]
Notation Forall2 := Vector92.Forall2 (only parsing).

#[deprecated(since="9.1", use=Vector92.Exists2)]
Notation Exists2 := Vector92.Exists2 (only parsing).

#[deprecated(since="9.1", use=Vector92.of_list)]
Fixpoint of_list {A} (l : list A) : t A (length l) :=
match l as l' return t A (length l') with
  |Datatypes.nil => []
  |(h :: tail)%list => (h :: (of_list tail))
end.

#[deprecated(since="9.1", use=Vector92.of_list)]
Lemma of_list_92 {A} l : @of_list A l = @Vector92.of_list A l.
Proof. induction l; cbn; f_equal; assumption. Qed.

#[deprecated(since="9.1", use=Vector92.to_list)]
Definition to_list {A}{n} (v : t A n) : list A :=
Eval cbv delta beta in fold_right (fun h H => Datatypes.cons h H) v Datatypes.nil.

#[deprecated(since="9.1", use=Vector92.of_list)]
Lemma to_list_92 {A} n v : @to_list A n v = @Vector92.to_list A n v.
Proof. induction v; cbn; f_equal; assumption. Qed.

Module VectorNotations.
Export Vector92.VectorNotations.
#[deprecated(since="9.1")]
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : vector_scope.
End VectorNotations.
