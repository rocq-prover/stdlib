From Stdlib Require Import Arith Morphisms RelationClasses.
Coercion is_true : bool >-> Sortclass.
#[global] Instance: Transitive leb.
Admitted.

Goal forall x y z, leb x y -> leb y z -> True.
  intros ??? H H'.
  lazymatch goal with
  | [ H : is_true (?R ?x ?y), H' : is_true (?R ?y ?z) |- _ ]
    => pose proof (transitivity H H' : is_true (R x z))
  end.
  exact I.
Qed.
