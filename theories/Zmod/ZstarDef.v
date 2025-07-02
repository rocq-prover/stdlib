From Stdlib Require Import ZArith Zdivisibility ZModOffset Lia.
From Stdlib Require Import Bool.Bool Lists.List.
Import ListNotations.
#[local] Open Scope Z_scope.
From Stdlib Require Import ZmodDef.

Module Zstar.
Import Zmod.

(** See [ZStarDef.Zmod.Zmod] for notes on efficient construction *)
#[projections(primitive)]
Record Zstar (m : Z) := mk {
  Private_to_Z : Z ;
  Private_range : Is_true (ZmodDef.Zmod.small Private_to_Z m &&
                             (Z.gcd Private_to_Z m =? 1)) }.
Arguments Private_to_Z {m}.
#[global] Add Printing Constructor Zstar.

Coercion to_Zmod {m : Z} (a : Zstar m) : Zmod m := Zmod.of_small_Z m (Private_to_Z a).

Definition of_coprime_Zmod_dep {m} (a : Zmod m) (H : True -> Z.gcd a m = 1) : Zstar m.
  refine (mk m (Zmod.to_Z a) (transparent_Is_true' _ (fun _ => _))).
  abstract (
    specialize (H I); specialize (Zmod.Private_range _ a); fold (@to_Z m a);
    case ZmodDef.Zmod.small; [intros|inversion 1]; cbn [andb];
    case Z.eqb_spec; try congruence).
Defined.

Definition of_Zmod {m} (x : Zmod m) : Zstar m.
  refine (of_coprime_Zmod_dep (if Z.eqb (Z.gcd x m) 1 then x else Zmod.one) (fun _ => _)).
abstract (
  case Z.eqb_spec; intros;
    cbv [Zmod.to_Z Zmod.Private_to_Z Zmod.of_Z Zmod.of_small_Z Zmod.one]; trivial;
    case ZmodDef.Zmod.small eqn:?;
    rewrite ?Z.gcd_mod_l, ?Z.gcd_1_l, ?Z.gcd_0_l; trivial;
    revert Heqb; cbv [ZmodDef.Zmod.small];
    specialize (Z.mod_bound_or 1 m); intuition try lia).
Defined.

Definition eqb {m} (x y : Zstar m) := Zmod.eqb x y.

Definition one {m} : Zstar m := of_Zmod Zmod.one.

Definition opp {m} (x : Zstar m) : Zstar m := of_Zmod (Zmod.opp x).

Definition abs {m} (x : Zstar m) : Zstar m := of_Zmod (Zmod.abs x).

Definition mul {m} (a b : Zstar m) : Zstar m.
  refine (of_coprime_Zmod_dep (Zmod.mul a b) (fun _ => _)).
abstract (
  case a as [a Ha], b as [b Hb] in *;
    cbv [Zmod.to_Z Zmod.mul Zmod.of_Z Zmod.of_small_Z Zmod.Private_to_Z];
  assert (ZmodDef.Zmod.small _ _ = true) as ->;
  [ set (Z.mul _ _) as z; specialize (Z.opp_mod_bound_or z m);
    cbv [ZmodDef.Zmod.small]; case m; cbn; intros; Z.div_mod_to_equations; lia
  | pose proof andb_prop_elim _ _ Ha as [A%Is_true_eq_true ?%Is_true_eq_true%Z.eqb_eq];
  pose proof andb_prop_elim _ _ Hb as [B%Is_true_eq_true ?%Is_true_eq_true%Z.eqb_eq];
  rewrite ?Z.gcd_mod_l, ?Z.coprime_mul_l; cbn; rewrite ?A, ?B; trivial ]).
Defined.

(**  Inverses and division have a canonical definition  *)

Definition inv {m} (x : Zstar m) : Zstar m := of_Zmod (Zmod.inv x).

Definition div {m} (x y : Zstar m) : Zstar m := mul x (inv y).

(**  Powers  *)

Definition pow {m} (a : Zstar m) z := of_Zmod (Zmod.pow a z).

Definition prod {m} xs : Zstar m := List.fold_right mul one xs.

(** Enumerating elements *)

Definition elements m : list (Zstar m) :=
  if Z.eqb m 0 then [one; opp one] else
  map of_Zmod (filter (fun x : Zmod _ => Z.eqb (Z.gcd x m) 1) (Zmod.elements m)).

Definition positives m :=
  map of_Zmod (filter (fun x : Zmod m => Z.gcd x m =? 1) (Zmod.positives m)).

Definition negatives m :=
  map of_Zmod (filter (fun x : Zmod m => Z.gcd x m =? 1) (Zmod.negatives m)).

End Zstar.

Notation Zstar := Zstar.Zstar.
