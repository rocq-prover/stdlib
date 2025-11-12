#[local] Set Universe Polymorphism.
From Stdlib Require Import Compat.Vector92 Compat.Fin92.

Section UniformElementType.
Context {A : Type}.

Fixpoint getFin {n : nat} (v : vec A n) {struct v} : fin n -> A :=
  match v with
  | nil => fun i => False_rect _ (inj_0 i)
  | cons a v => fun i =>
    match i in fin n return vec _ (pred n) -> A with
    | finO => fun _ => a
    | finS i => fun v => getFin v i
    end v
  end.

Fixpoint putFin {n} (v : vec A n) {struct v} : fin n -> A -> vec A n :=
  match v with
  | nil => fun _ _ => nil
  | cons b v => fun i =>
    match i in fin n return vec _ (pred n) -> _ -> vec _ n with
    | finO => fun v a => cons a v
    | finS i => fun v a => cons b (putFin v i a)
    end v
  end.

Definition getLt {n} (v: vec A n) {p} (H: p < n) := getFin v (Fin92.of_nat _ _ H).
Definition putLt {n} (v: vec A n) {p} (H: p < n) := putFin v (Fin92.of_nat _ _ H).
End UniformElementType.

Lemma nth_error_to_list [A n] (v : vec A n) i : List.nth_error v (to_nat i) = Some (getFin v i).
Proof. induction v; [case Fin92.inj_0 | case (Fin92.inj_S i) as [->|[? ->] ] ]; cbn; eauto. Qed.
