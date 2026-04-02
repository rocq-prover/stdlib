(** The example in the Reference Manual *)

From Stdlib Require Import ZArith.

Search Z.mul Z.add "distr".
Search "+"%Z "*"%Z "distr" -positive -Prop.
Search (?x * _ + ?x * _)%Z outside Lia.
