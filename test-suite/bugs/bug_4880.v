From Stdlib Require Import Reals Nsatz.
#[local] Open Scope R.

Goal forall x y : R,
  x*x =  y *  y ->
  x*x = -y * -y ->
  x*(x*x) = 0 -> (* The associativity does not actually matter, *)
  (x*x)*x = 0.   (* just otherwise [assumption] would solve the goal. *)
Proof.
  nsatz.
Qed.
