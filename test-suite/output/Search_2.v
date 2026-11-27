From Stdlib Require Import PeanoNat.

Search (_ ?n ?m = _ ?m ?n).
(* Ignore the gcd equation added by Rocq PR #22579, so these search
   results remain the same with both prelude definitions. *)
Search "'mod'" -"mod" -"gcd_S".
Search "mod"%nat -"mod" -"gcd_S".
