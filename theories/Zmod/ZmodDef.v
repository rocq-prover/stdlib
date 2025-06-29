From Stdlib Require Import BinNatDef BinInt Bool List Zcong.
Import ListNotations.
#[local] Open Scope Z_scope.

Module Zmod.

(** [small z m = true <-> z mod m = z], but [small] is efficiently computable
   through a single arbitrary-precision comparison.  *)
#[local] Definition small z m :=
  (0 =? m) || negb (Z.sgn z =? -Z.sgn m) && (Z.abs z <? Z.abs m).

(** [Zmod m] is isomorphic to [{ z | z mod m = z}]. For efficiency, it is
   constructed from scratch as
  - a dedicated record type instead of [sig], to avoid repeating the
    subset-membership predicate in constructor arguments
  - with primitive projections, to avoid the modulus in projection arguments
  - using [Is_true] instead of [_ = true] to avoid repeating modulus in values
  - using [small] instead of [Z.modulo] to speed up type-checking of values.
  This construction is [not] a part of the supported interface of [Zmod], so
  the projections are named as [Private_] to exclude them from Search, instead
  presenting wrappers with types that do not reveal these optimoizations are. *)
#[projections(primitive)]
Record Zmod (m : Z) := mk {
  Private_to_Z : Z ; Private_range : Bool.Is_true (small Private_to_Z m) }.
Arguments Private_to_Z {m}.
#[global] Add Printing Constructor Zmod.

Definition of_small_Z (m : Z) (z : Z) : Zmod m.
  refine (mk m (if small z m then z else 0)
               (transparent_Is_true' _ (fun _ => _))).
  abstract (case (small z m) eqn:H; rewrite ?H; case m; trivial).
Defined.

Definition of_Z (m : Z) (z : Z) : Zmod m := of_small_Z m (z mod m).

Coercion unsigned {m} (x : Zmod m) := Private_to_Z x.
Notation to_Z := unsigned (only parsing).

Definition signed {m} (x : Zmod m) : Z :=
  if Z.ltb (Z.double (Z.abs x)) (Z.abs m) then x else x-m.

Definition zero {m} := of_Z m 0.

Definition one {m} := of_Z m 1.

(** ** Ring operations *)

Definition eqb {m} (x y : Zmod m) := Z.eqb (to_Z x) (to_Z y).

Definition add {m} (x y : Zmod m) : Zmod m := (* (x+y) mod m *)
  let n := x + y in
  let n := if Z.ltb (Z.abs n) (Z.abs m) then n else n-m in
  of_small_Z m n.

Definition sub {m} (x y : Zmod m) : Zmod m := (* (x-y) mod m *)
  let z := x - y in
  let z := if Z.sgn z =? -Z.sgn m then z+m else z in
  of_small_Z m z.

Definition opp {m} (x : Zmod m) : Zmod m := sub zero x.

Definition mul {m} (x y : Zmod m) : Zmod m := of_Z m (x * y).

(** ** Three notions of division *)

Definition udiv {m} (x y : Zmod m) : Zmod m :=
  if Z.eq_dec 0 y then opp one else
  let z := Z.div x y in
  let z := if Z.sgn z =? -Z.sgn m then z+m else z in
  of_small_Z m z.

Definition umod {m} (x y : Zmod m) : Zmod m :=
  of_small_Z m (Z.modulo (unsigned x) (unsigned y)).

Definition squot {m} (x y : Zmod m) :=
  of_Z m (if signed y =? 0 then -1 else Z.quot (signed x) (signed y)).

Definition srem {m} (x y : Zmod m) := of_Z m (Z.rem (signed x) (signed y)).

Definition inv {m} (x : Zmod m) : Zmod m := of_small_Z m (Z.invmod (to_Z x) m).

Definition mdiv {m} (x y : Zmod m) : Zmod m := mul x (inv y).

(** ** Powers  *)

#[local] Definition Private_pow_N {m} (a : Zmod m) n := N.iter_op mul one a n.
Definition pow {m} (a : Zmod m) z :=
  if Z.ltb z 0 then inv (Private_pow_N a (Z.to_N (Z.opp z))) else Private_pow_N a (Z.to_N z).

(** ** Bitwise operations *)
Definition and {m} (x y : Zmod m) := of_Z m (Z.land x y).

Definition ndn {m} (x y : Zmod m) := of_Z m (Z.ldiff x y).

Definition or {m} (x y : Zmod m) := of_Z m (Z.lor x y).

Definition xor {m} (x y : Zmod m) := of_Z m (Z.lxor x y).

Definition not {m} (x : Zmod m) := of_Z m (Z.lnot (to_Z x)).

Definition abs {m} (x : Zmod m) := if signed x <? 0 then opp x else x.

(** ** Shifts *)

Definition slu {m} (x : Zmod m) n := of_Z m (Z.shiftl x n).

Definition sru {m} (x : Zmod m) n := of_Z m (Z.shiftr x n).

Definition srs {m} x n := of_Z m (Z.shiftr (@signed m x) n).

(** ** Bitvector operations that vary the modulus *)

(** Effective use of the operations defined here with moduli that are not
   convertible to values requires substantial understanding of dependent types,
   in particular the equality type, the sigma type, and their eliminators. Even
   so, many applications are better served by [Z] or by adopting one
   common-denominator modulus. See the four variants of [skipn_app] and
   [app_assoc], for a taste of the challenges. *)

#[local] Notation bits n := (Zmod (2^n)).

Definition app {n m} (a : bits n) (b : bits m) : bits (n+m) :=
  of_Z _ (Z.lor a (Z.shiftl b n)).

Definition firstn n {w} (a : bits w) : bits n := of_Z _ a.

Definition skipn n {w} (a : bits w) : bits (w-n) := of_Z _ (Z.shiftr a n).

Definition slice start pastend {w} (a : bits w) : bits (pastend-start) :=
  firstn (pastend-start) (skipn start a).

(** ** Enumerating elements *)

Definition elements m : list (Zmod m) :=
  map (fun i => of_Z m (Z.of_nat i)) (seq 0 (Z.abs_nat m)).

Definition positives m :=
  let p := (Z.abs m - Z.b2z ((0 <? m)))/2 in
  map (fun i => of_Z m (Z.of_nat i)) (seq 1 (Z.to_nat p)).

Definition negatives m :=
  let p := (Z.abs m - Z.b2z ((0 <? m)))/2 in
  let r := Z.abs m - 1 - p in
  map (fun i => of_Z m (Z.of_nat i)) (seq (S (Z.to_nat p)) (Z.to_nat r)).

Definition invertibles m : list (Zmod m) :=
  if Z.eqb m 0 then [one; opp one] else
  filter (fun x : Zmod _ => Z.eqb (Z.gcd x m) 1) (elements m).

End Zmod.

Notation Zmod := Zmod.Zmod.

Notation bits n := (Zmod (2^n)).

Module bits.
  Notation of_Z n z := (Zmod.of_Z (2^n) z).
End bits.

Declare Scope Zmod_scope.
Delimit Scope Zmod_scope with Zmod.
Bind Scope Zmod_scope with Zmod.
Notation "0" := Zmod.zero : Zmod_scope.
Notation "1" := Zmod.one : Zmod_scope.
Infix "+" := Zmod.add : Zmod_scope.
Infix "-" := Zmod.sub : Zmod_scope.
Notation "- x" := (Zmod.opp x) : Zmod_scope.
Infix "*" := Zmod.mul : Zmod_scope.
Infix "^" := Zmod.pow : Zmod_scope.
