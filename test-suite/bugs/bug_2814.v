From Stdlib Require Import Program.

Goal forall (x : Type) (f g : Type -> Type) (H : JMeq (f x) (g x)), f x -> g x.
  intros.
  induction H.
  assumption.
Qed.
