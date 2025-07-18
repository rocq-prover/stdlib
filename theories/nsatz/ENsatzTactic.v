(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*
 Tactic ensatz: proofs of polynomials equalities in an integral domain
 (commutative ring without zero divisor) with existential quantifier or
 existential variables.

 Examples: see test-suite/success/ENsatz.v and test-suite/success/EENsatz.v

*)

From Stdlib Require Import BinPos.
From Stdlib Require Import BinList.
From Stdlib Require Import BinNat.
From Stdlib Require Import BinInt.
From Stdlib Require Import Ncring.
From Stdlib Require Import NsatzTactic.

Section ensatz.

  Context {R:Type}`{Rid:Integral_domain R}.

  Local Fixpoint LTType {A: Type} (B : Type) (l : list A) {struct l} : Type :=
    match l with
    | nil => unit
    |  _ :: l0 =>  (B * LTType B l0)%type
    end.

  Local Fixpoint Cond0
    (A : Type) (Interp : A -> R) (l : list A) {struct l} : (LTType A l -> R) :=
    match l return (LTType A l -> R) with
    | nil => fun _ => ring0
    | a :: l0 =>
        fun n => add (mul (Interp (fst n)) (Interp a))
                   (Cond0 A Interp l0 (snd n))
    end.

  Local Fixpoint ring0_tuple (A :Type) (l: list A) : LTType R l :=
    match l return (LTType R l) with
    | nil => tt
    | a :: q => (ring0, ring0_tuple A q)
    end.

  Local Fixpoint add_coef
    (l: list PolZ)  (a : list PolZ) (c : PolZ)
    {struct l} : (LTType PolZ l -> LTType PolZ l) :=
    match l, a return  (LTType PolZ l -> LTType PolZ l) with
    | nil, _ => (fun _ => tt)
    | _, nil => (fun x => x)
    | _ :: q , hx :: qx =>
        let coef := PolZmul c hx in
        fun x => (PolZadd coef (fst x), add_coef q qx c (snd x))
    end.

  Local Fixpoint certi_aux
    (lpe: list PolZ) (lq: list PEZ): LTType PolZ lpe :=
    match lpe, lq return (LTType PolZ lpe) with
    |  nil, _ => tt
    |  h::q, nil=> (P0Z, certi_aux q lq)
    |  h1::q1, h2::q2=> (norm h2, certi_aux q1 q2 )
    end.

  Local Fixpoint certi
    (lla : list (list PEZ)) (lpe: list PolZ) (lq: list PEZ) : LTType PolZ lpe :=
    match lla return (LTType PolZ lpe) with
    | nil => certi_aux lpe lq
    | h::q =>
        let l := certi q ((mult_l h lpe) :: lpe) lq in
        add_coef lpe (map norm h) (fst l) (snd l)
    end.

  Local Definition PhiR := @PhiR R ring0 ring1 add mul opp.

  Local Lemma factories_compute_list :
    forall lla l lpe lq,
      PhiR l (mult_l lq (compute_list lla lpe)) ==
        Cond0 PolZ (PhiR l) lpe (certi lla lpe lq).
  Proof.
    induction lla.
    - induction lpe.
      + destruct lq;simpl; reflexivity.
      + destruct lq;simpl; simpl in IHlpe.
        * specialize (IHlpe nil) as H.
          rewrite <- H.
          cring.
        * specialize (IHlpe lq) as H.
          unfold PhiR.
          rewrite  PolZadd_correct.
          rewrite PolZmul_correct.
          rewrite <- H.
          cring.
    - intros. simpl.
      specialize (IHlla l (mult_l a lpe :: lpe) lq) as H.
      simpl in H.
      remember (fst (certi lla (mult_l a lpe :: lpe) lq)) as r.
      remember (snd (certi lla (mult_l a lpe :: lpe) lq)) as l0.
      clear Heql0. clear Heqr.
      rewrite H. clear H.
      revert l0; revert lpe.
      induction a.
      + intros;destruct lpe; simpl; cring.
      + intros.
        destruct lpe;[ cring |].
        simpl.
        specialize (IHa lpe).
        rewrite <- IHa.
        repeat setoid_rewrite PolZadd_correct.
        repeat setoid_rewrite PolZmul_correct.
        cring.
  Qed.

  (* The type of the existential *)

  Local Fixpoint LTEType
    {A : Type} (B: Type) (l : list (bool * A)) {struct l} : Type :=
    match l with
    | nil => unit
    | (true, _) :: l0 =>  (B * LTEType B l0)%type
    | (false, _) :: l0 =>  LTEType B l0
    end.

  Local Fixpoint btype_to_ftype
    (A B : Type) (norm :  A -> B) (l: list (bool*A))
    {struct l} : (LTType B (map norm (map snd l)) -> LTEType B l) :=
    match l return  (LTType B (map norm (map snd l)) -> LTEType B l) with
    | nil => fun _ => tt
    | (true, _) :: q =>  fun x => (fst x, btype_to_ftype A B norm  q (snd x))
    | (false, _) :: q =>  fun x => (btype_to_ftype A B norm q (snd x))
    end.

  Local Definition cert (lpe: list (prod bool PEZ)) lci lq:=
    let p := certi lci (map norm (map snd lpe)) lq in
    btype_to_ftype PEZ PolZ norm lpe p.

  (* For the assumptions *)

  Local Fixpoint mk_HCond0
    {A : Type} (Interp : A -> R) (l : list (bool * A)) {struct l} : Prop :=
    match l with
    | nil => True
    | (true, a) :: l0 => (mk_HCond0 Interp l0)
    | (false, a) :: l0 => ((Interp a) == 0) /\ (mk_HCond0 Interp l0)
    end.

  (* For the conclusion *)

  Local Fixpoint GCond0
    {A B : Type} (Interp : A -> R) (Interp' : B -> R) (l : list (bool * A))
    {struct l} : (LTEType B l -> R) :=
    match l return (LTEType B l -> R) with
    | nil => (fun _ => ring0)
    | (true, a) :: l0 => (fun n => add (mul (Interp' (fst n)) (Interp a))
                                (GCond0 Interp Interp' l0 (snd n)))
    | (false, a) :: l0 => GCond0 Interp Interp' l0
    end.

  Local Lemma check_correct:
    forall l lpe qe lci lq ,
      check (map snd lpe) qe (lci,lq) = true ->
      mk_HCond0 (PEevalR l) lpe ->
      (PEevalR l qe) == GCond0 (PEevalR l) (PhiR l) lpe (cert lpe lci lq).
  Proof.
    unfold cert.
    unfold check;intros l lpe qe lla lq H2 H1.
    apply PolZeq_correct with (l:=l) in H2.
    specialize (factories_compute_list lla l (map norm (map snd lpe)) lq) as H.
    rewrite H in H2.
    clear H.
    rewrite norm_correct.
    rewrite H2.
    clear H2.
    remember (certi lla (map norm (map snd lpe)) lq) as x eqn: Hx.
    clear Hx.
    induction lpe.
    - cring.
    - destruct a.
      destruct b.
      + simpl in H1.
        specialize (IHlpe H1 (snd x)).
        simpl.
        rewrite IHlpe.
        rewrite norm_correct.
        reflexivity.
      + destruct H1.
        specialize (IHlpe H0 (snd x)).
        simpl.
        rewrite IHlpe.
        unfold PhiR.
        rewrite <- norm_correct.
        rewrite H.
        cring.
  Qed.

  Local Fixpoint inter
    {A B: Type} (Interp: B -> R) (l: list (bool*A)) {struct l} : (LTEType B l -> LTEType R l) :=
    match l return (LTEType B l -> LTEType R l) with
    | nil => fun _ => tt
    | (true, _) :: q => fun x => (Interp (fst x), inter Interp q (snd x))
    | (false, _) :: q => fun x => inter Interp q x
    end.

  Local Lemma check_correct_exists :
    forall l lpe qe lci lq ,
      check (map snd lpe) qe (lci,lq) = true ->
      mk_HCond0 (PEevalR l) lpe ->
      exists n, ((PEevalR l qe) == GCond0 (PEevalR l) (fun x => x) lpe n).
  Proof.
    intros * H1 H2.
    exists (inter (PhiR l) lpe (cert lpe lci lq)).
    rewrite (check_correct _ _ _ _ _ H1 H2).
    remember (cert lpe lci lq) as x eqn: Hx.
    clear H1 H2 Hx.
    induction lpe.
    - reflexivity.
    - destruct a.
      destruct b; simpl; rewrite <- IHlpe; reflexivity.
  Qed.

End ensatz.

Module Mk_pl.

  Local Fixpoint set_false (l: list (PExpr Z)) :=
    match l with
    | nil => nil
    | h :: q => (false, h) :: (set_false q)
    end.

  Local Fixpoint set_true (l: list (PExpr Z)) :=
    match l with
    | nil => nil
    | h :: q => (true, h) :: (set_true q)
    end.

  Ltac mk_pl lp21 n :=
    let lp21 := eval compute in (List.rev lp21) in
    let hd   := eval compute in (firstn n lp21) in
    let hdt  := eval compute in (set_true hd) in
    let tl   := eval compute in (skipn n lp21) in
    let tlf  := eval compute in (set_false tl) in
    let pl   := eval compute in (hdt ++ tlf) in
    eval compute in (List.rev pl).

End Mk_pl.

Section poly_sort.
  Context {T:Type}.
  Context (equal : T -> T -> comparison).

  Inductive MPoly : Type:=
  | Poly : MPoly -> (PExpr Z) -> T -> MPoly
  | Pc : (PExpr Z) -> MPoly.

  Local Fixpoint mult_mpoly (c : PExpr Z) (p : MPoly) : MPoly :=
    match p with
    | Pc e => Pc (PEmul e c)
    | Poly p e v => Poly (mult_mpoly c p) (PEmul e c) v
    end.

  Inductive Monom : Type:=
  | Mon : (PExpr Z) -> T -> Monom
  | Monc : (PExpr Z) -> Monom.

  Local Fixpoint add_monom_poly (p: MPoly) (m: Monom) :=
    match p with
    | Pc e1 =>
        match m with
        | Monc e2 => Pc (PEadd e1 e2)
        | Mon e2 v => Poly p e2 v
        end
    | Poly p' e1 v1 =>
        match m with
        | Monc e2 => Poly (add_monom_poly p' m) e1 v1
        | Mon e2 v2 =>
            match equal v1 v2 with
            | Eq => Poly p' (PEadd e1 e2) v1
            | Gt => Poly (add_monom_poly p' m) e1 v1
            | Lt => Poly p e2 v2
            end
        end
    end.

  Local Fixpoint add_mpoly (p1 p2 : MPoly) : MPoly :=
    match p1 with
    | Pc e1 => add_monom_poly p2 (Monc e1)
    | Poly p1' e1 v1 => add_mpoly p1' (add_monom_poly p2 (Mon e1 v1))
    end.

  Local Fixpoint opp_mpoly (p: MPoly) : MPoly :=
    match p with
    | Pc e => Pc (PEopp e)
    | Poly p e v => Poly (opp_mpoly p) (PEopp e) v
    end.

  Local Fixpoint get_coef (p: MPoly) :=
    match p with
    | Pc e => e :: nil
    | Poly p e v => e :: get_coef p
    end.

End poly_sort.

Module Ensatz_solve.

  Local Ltac mk_tuple R l f :=
    match l with
    | (?a :: ?h) =>
        let t := mk_tuple R h f in
        constr:((t, f a))
    | (?a1 :: ?a2 :: @nil R) => constr:((f a2,f a1))
    end.

  Local Ltac destr_tuple R l f :=
    match goal with
    | x : (R * ?A)%type |- _ =>
        let z := fresh "z" in
        destruct x as [z x];
        let l := constr:(z :: l) in
        destr_tuple R l f
    | x : (unit)%type |- _ =>
        let l := eval compute in (l) in
        let t := mk_tuple R l f in
        exists t
     end.

  Ltac mk_exists R x f :=
    match goal with
    | x : (R * unit)%type |- _ =>
        let z := fresh "z" in
        destruct x as [z x]; exists (f z)
    | x : (R * ?A)%type |- _ =>
        destr_tuple R constr:(@nil R) f
    end.

  Ltac ensatz_solve cr R p2 lp2 n fv info :=
    let p21 := fresh "p21" in
    let lp21 := fresh "lp21" in
    let n21 := fresh "n21" in
    let lv := fresh "lv" in
    set (p21:=p2); set (lp21:=lp2); set (n21:= n); set(lv := fv);
    (*We want r to be 1, so we set radicalmax to 1*)
    NsatzTactic.nsatz_call 1%N info 0%Z p2 lp2
      ltac:(fun c r lq lci =>
              let Hg := fresh "Hg" in
              let c21 := fresh "c" in
              set (c21 := c);
              let p211 := constr: (PEmul c p21) in
              let pl := Mk_pl.mk_pl lp21 n in
              (*If c is not 1/-1, this assert should fail*)
              assert (Hg:check lp21 p211 (lci,lq) = true);
              [vm_compute; reflexivity |];
              assert (Hg2: mk_HCond0 (PEevalR lv) pl);
              [repeat (split;[assumption|idtac]); exact I|];
              generalize (@check_correct_exists
                            _ _ _ _ _ _ _ _ _ _ _
                            lv pl p211 lci lq Hg Hg2);
              let x := fresh "x" in
              let H1 := fresh "H" in
              intros [x H1];
              cbv delta [LTEType] iota beta match in x;
              match c with
              | PEc((-1)%Z) => mk_exists R x constr:(fun x:R => -x);
                              symmetry in H1
              | PEc(1%Z) => mk_exists R x constr:(fun x:R => x)
              end;
              cbv delta [lv p21] in H1;
              cbv delta
                [PEevalR
                   GCond0
                   Ring_polynom.PEeval
                   gen_phiZ gen_phiPOS
                   InitialRing.gen_phiZ
                   InitialRing.gen_phiPOS
                   BinList.nth
                   jump fst snd hd]
                iota beta match in H1;
               repeat unfold snd;
               repeat unfold fst;
               apply NsatzTactic.psos_r1b;
               NsatzTactic.equalities_to_goal cr;
               intros <-; cring
           ).

  Module Reifi.

    Inductive Var {A: Type}: Type :=
    | mRef: A -> Var
    | fstVar : forall B, @Var (A*B) -> @Var A
    | sndVar : forall B, @Var (B*A) -> @Var A.

    Local Ltac reify_evar_aux term :=
      match term with
      | (fun e => fst (@?P e)) =>
          let term' := reify_evar_aux P in
          constr:(fun x => @fstVar _ _ (term' x))
      | (fun e => snd (@?P e)) =>
          let term' := reify_evar_aux P in
          constr:(fun x => @sndVar _ _ (term' x))
      | (fun e:?T => e) => constr:(fun e :T => mRef e)
      end.

    Local Ltac reify_evar R term :=
      match term with
      | (fun e => fst _) =>
          let term' := reify_evar_aux term in
          constr:
            (fun e' =>
               @Poly (@Var R) (@Pc (@Var R) (PEc 0%Z)) (PEc 1%Z) (term' e'))
      | (fun e => snd _) =>
          let term' := reify_evar_aux term in
          constr:
            (fun e' =>
               @Poly (@Var R) (@Pc (@Var R) (PEc 0%Z)) (PEc 1%Z) (term' e'))
      | (fun e:?T => e) =>
          constr:
            (fun e':T =>
               @Poly (@Var T) (@Pc (@Var T) (PEc 0%Z)) (PEc 1%Z) (mRef e'))
      end.

    Local Fixpoint equal
      {A1 A2: Type} (v1 : @Var A1) (v2 : @Var A2): comparison :=
      match v1, v2 with
      | mRef _, mRef _ => Eq
      | fstVar _ v1, fstVar _ v2 => equal v1 v2
      | sndVar _ v1, sndVar _ v2 => equal v1 v2
      | fstVar _ _, sndVar _ _ => Gt
      | sndVar _ _, fstVar _ _ => Lt
      | _, mRef _ => Gt
      | mRef _, _ => Lt
      end.

    Local Definition add_mpoly
      {A: Type} (p1 p2 : @MPoly (@Var A)) : @MPoly (@Var A):=
      add_mpoly equal p1 p2.

    Local Ltac reify R Tring lvar term:=
      match open_constr:((Tring, term)) with
      | (Ring (T:=?R) (add:=?add) (mul:=?mul) (sub:=?sub),
          (fun e1 => ?op (@?E1 e1) (@?E2 e1))) =>
          let _ := match goal with _ => convert add op end in
          let E1' := reify R Tring lvar E1 in
          let E2' := reify R Tring lvar E2 in
          constr:(fun x => add_mpoly (E1' x) (E2' x))
      | (Ring (T:=?R) (add:=?add) (mul:=?mul) (sub:=?sub),
          (fun e1 => ?op (@?E1 e1) (@?E2 e1))) =>
          let _ := match goal with _ => convert sub op end in
          let E1' := reify R Tring lvar E1 in
          let E2' := reify R Tring lvar E2 in
          constr:(fun x => add_mpoly (E1' x) (opp_mpoly (E2' x)))
      | (Ring (T:=?R) (ring0:=?ring0) (ring1:=?ring1)
           (add:=?add) (mul:=?mul) (sub:=?sub) (opp:=?opp),
          (fun e1 => ?op ?E (@?E1 e1))) =>
          let _ := match goal with _ => convert mul op end in
          let E1' := reify R Tring lvar E1 in
          let E' := reify_term R ring0 ring1 add mul sub opp lvar E in
          constr:(fun x => mult_mpoly E' (E1' x))
      | (Ring (T:=?R) (ring0:=?ring0) (ring1:=?ring1)
           (add:=?add) (mul:=?mul) (sub:=?sub) (opp:=?opp),
          (fun e1 => ?op (@?E1 e1) ?E)) =>
          let _ := match goal with _ => convert mul op end in
          let E1' := reify R Tring lvar E1 in
          let E' := reify_term R ring0 ring1 add mul sub opp lvar E in
          constr:(fun x => mult_mpoly E' (E1' x))
      | (_, (fun e => @?E e)) => reify_evar R E
      | (Ring (T:=?R) (opp:=?opp), (fun e => ?op (@?E e))) =>
          let _ := match goal with _ => convert opp op end in
          let E' := reify_evar R E in
          constr:(fun x => opp_mpoly (E' x))
      | (Ring (T:=?R) (ring0:=?ring0) (ring1:=?ring1)
           (add:=?add) (mul:=?mul) (sub:=?sub) (opp:=?opp),
          (fun _:?T => ?E)) =>
          let E' := reify_term R ring0 ring1 add mul sub opp lvar E in
          constr:(fun _:T => @Pc (@Var R) E')
      end.

    Local Definition coef {A R:Type} (p: A -> @MPoly (@Var R)) :=
      fun x => get_coef (p x).

    Local Definition merge {A R:Type} (p1 p2: A -> @MPoly (@Var R)) :=
      fun x => add_mpoly (p1 x) (opp_mpoly (p2 x)).

    Ltac reify_goal  :=
      match goal with
      | |- @ex _ (fun e1 : _ => @eq ?R (@?P1 e1) (@?P2 e1)) =>
          let lvar := open_constr:(_ :> list R) in
          let R_ring := constr:(_ :> Ring (T:=R)) in
          let Tring := type of R_ring in
          let xl := reify R Tring lvar P1 in
          let xr := reify R Tring lvar P2 in
          let x :=
            eval cbv delta
              [merge
                 coef
                 get_coef
                 add_mpoly
                 ENsatzTactic.add_mpoly
                 mult_mpoly
                 add_monom_poly
                 equal
                 opp_mpoly]
              beta iota in (coef (merge xr xl))
           in
           constr:((lvar,x))
      end.

  End Reifi.

  Ltac hterm R g :=
    match g with
    | (exists _: _, _ ) => constr:((@nil R))
    | ?b1 == ?b2 -> ?g =>
        let l := hterm R g in
        constr:((b1 :: l))
    end.

End Ensatz_solve.

Module Eensatz_solve.

  Local Ltac econstrain_aux R ring0 ring1 add mul opp l lc lv z:=
    match open_constr:((lc, lv)) with
    |((?c, ?q1), @cons _ ?v ?q2) =>
       let c := eval cbv delta [l]in (@PhiR R ring0 ring1 add mul opp l c) in
       let c :=
         eval cbv delta
           [PhiR
              NsatzTactic.PhiR
              Pphi
              gen_phiZ
              gen_phiPOS
              pow_pos
              jump hd tl]
           iota beta match in c
       in
       let v := eval cbv delta [l] in (PEevalR l v) in
       let v :=
         eval cbv delta
           [PEevalR
              GCond0
              Ring_polynom.PEeval
              gen_phiZ gen_phiPOS
              InitialRing.gen_phiZ
              InitialRing.gen_phiPOS
              BinList.nth
              jump tl fst snd hd]
           iota beta match in v
       in
       assert (v = z * c) by reflexivity;
       econstrain_aux R ring0 ring1 add mul opp l q1 q2 z
    | (_, _) => idtac
    end.

  Local Ltac econstrain R l lc lv z :=
    let R_ring := constr:(_ :> Ring (T:=R)) in
    let Tring := type of R_ring in
    lazymatch Tring with
      | Ring (T:=?R) (ring0:=?ring0) (ring1:=?ring1)
          (add:=?add) (mul:=?mul) (sub:=?sub) (opp:=?opp) =>
          econstrain_aux R ring0 ring1 add mul opp l lc lv z
    end.

  Ltac ensatz_solve R p2 lp2 n fv vs info :=
    let p21 := fresh "p21" in
    let lp21 := fresh "lp21" in
    let lv := fresh "lv" in
    let lvs := fresh "lvs" in
    set (p21:=p2);set (lp21:=lp2); set(lv := fv); set (lvs := vs);
    (*We want r to be 1, so we set radicalmax to 1*)
    NsatzTactic.nsatz_call 1%N info 0%Z p2 lp2
      ltac:(fun c r lq lci =>
              let Hg := fresh "Hg" in
              let c21 := fresh "c" in
              let p211 := constr: (PEmul c p21) in
              let pl := Mk_pl.mk_pl lp21 n in
              (*If c is not 1/-1, this assert should fail*)
              assert (Hg:check lp21 p211 (lci,lq) = true);
              [vm_compute; reflexivity |];
              assert (Hg2: mk_HCond0 (PEevalR lv) pl);
              [repeat (split;[assumption|idtac]); exact I|];
              generalize (@check_correct
                            _ _ _ _ _ _ _ _ _ _ _
                            lv pl p211 lci lq Hg Hg2);
              let Hc := fresh "Hc" in
              intro Hc;
              let Cert := fresh "Cert" in
              let cert := constr: (cert pl lci lq) in
              set (Cert := cert);
              specialize (eq_refl Cert);
              unfold Cert at 2;
              let HCert := fresh "HCert" in
              intro HCert;
              fold Cert in Hc;
              compute in Cert;
              let y := eval simpl in (map (PEevalR lv) vs) in
              let cert := eval cbv delta [Cert] in Cert in
              match c with
              | PEc ((-1)%Z) => econstrain R lv cert vs ((-1)%Z);
                               symmetry in Hc
              | PEc (1%Z) => econstrain R lv cert vs (1%Z)
              end;
              cbv delta [Cert lv p21] in Hc;
              cbv delta
                [PEevalR
                   GCond0
                   Ring_polynom.PEeval
                   gen_phiZ gen_phiPOS
                   InitialRing.gen_phiZ
                   InitialRing.gen_phiPOS
                   BinList.nth
                   jump tl fst snd hd]
               iota beta match in Hc;
               cbv delta
                 [PhiR
                    NsatzTactic.PhiR
                    Pphi gen_phiZ
                    gen_phiPOS
                    pow_pos
                    jump hd tl]
               iota beta match in Hc;
              apply NsatzTactic.psos_r1b;
              apply psos_r1 in Hc;
              rewrite <- Hc;
              cring
           ).

  Module Reifi.

    Local Definition add_mpoly (p1 p2 : @MPoly positive) : @MPoly positive:=
      add_mpoly Pos.compare p1 p2.

    Local Ltac areify R Tring lvar term:=
      match open_constr:((Tring, term)) with
      | (Ring
           (T:=?R) (ring0:=?ring0) (ring1:=?ring1)
           (add:=?add) (mul:=?mul) (sub:=?sub) (opp:=?opp), ?E) =>
          let __ := match E with _ => is_ground E end in
          let E' := reify_term R ring0 ring1 add mul sub opp lvar E in
          constr:((@Pc positive E'))
      | (Ring
           (T:=?R) (ring0:=?ring0) (ring1:=?ring1)
           (add:=?add) (mul:=?mul) (sub:=?sub) (opp:=?opp), ?E) =>
          let __ := match E with _ => is_evar E end in
          let E' := reify_term R ring0 ring1 add mul sub opp lvar E in
          let n :=
            match E' with
            | PEX _ ?n => n
            end
          in
          constr:(@Poly positive (@Pc positive (PEc 0%Z)) (PEc 1%Z) n)
      | (Ring
           (T:=?R) (ring0:=?ring0) (ring1:=?ring1)
           (add:=?add) (mul:=?mul) (sub:=?sub) (opp:=?opp), ?op ?E1 ?E2) =>
          let _ := match goal with _ => convert mul op end in
          let _ := match E1 with _ => is_ground E1 end in
          let _ := match E2 with _ => has_evar E2 end in
          let E1' := reify_term R ring0 ring1 add mul sub opp lvar E1 in
          let E2' := areify R Tring lvar E2 in
          constr:(mult_mpoly E1' E2')
      | (Ring
           (T:=?R) (ring0:=?ring0) (ring1:=?ring1)
           (add:=?add) (mul:=?mul) (sub:=?sub) (opp:=?opp), ?op ?E1 ?E2) =>
          let _ := match goal with _ => convert mul op end in
          let _ := match E1 with _ => has_evar E1 end in
          let _ := match E2 with _ => is_ground E2 end in
          let E1' := areify R Tring lvar E1 in
          let E2' := reify_term R ring0 ring1 add mul sub opp lvar E2 in
          constr:(mult_mpoly E2' E1')
      | (Ring
           (T:=?R) (add:=?add) (mul:=?mul) (sub:=?sub)
           (opp:=?opp), ?op ?E1 ?E2) =>
          let _ := match goal with _ => convert add op end in
          let E1' := areify R Tring lvar E1 in
          let E2' := areify R Tring lvar E2 in
          constr:(add_mpoly E1' E2')
      | (Ring (T:=?R) (add:=?add) (mul:=?mul) (sub:=?sub), ?op ?E1 ?E2) =>
          let _ := match goal with _ => convert sub op end in
          let E1' := areify R Tring lvar E1 in
          let E2' := areify R Tring lvar E2 in
          constr:(add_mpoly E1' (opp_mpoly E2'))
      | (Ring (T:=?R) (ring0:=?ring0) (ring1:=?ring1)
           (add:=?add) (mul:=?mul) (sub:=?sub) (opp:=?opp), (?op ?E)) =>
          let _ := match goal with _ => convert opp op end in
          let _ := match E with _ => is_evar E end in
          let E' := reify_term R ring0 ring1 add mul sub opp lvar E in
          let n := match E' with
                   | PEX _ ?n => n
                   end
          in
          constr:(opp_mpoly(@Poly positive (@Pc positive (PEc 0%Z)) (PEc 1%Z) n))
      end.

    Local Fixpoint get_var (p: @MPoly positive) :=
      match p with
      | Pc e => nil
      | Poly p e v => (PEX Z v) :: get_var p
      end.

    Ltac reify_goal  :=
      match goal with
      | |- @eq ?R ?E1 ?E2 =>
          let lvar := open_constr:(_ :> list R) in
          let R_ring := constr:(_ :> Ring (T:=R)) in
          let Tring := type of R_ring in
          let xl := areify R Tring lvar E1 in
          let xr := areify R Tring lvar E2 in
          let poly := eval vm_compute in (add_mpoly xr (opp_mpoly xl)) in
          let x := eval vm_compute in (get_coef poly) in
          let v := eval vm_compute in (get_var poly) in
          constr:((lvar,x, v))
      end.

  End Reifi.

  Ltac hterm R g :=
    match g with
    | ?b1 = ?b2 => constr:((@nil R))
    | ?b1 == ?b2 -> ?g =>
        let l := hterm R g in
        constr:((b1 :: l))
    end.

End Eensatz_solve.

Local Ltac reify_h lv lb :=
  match lb with
  | @nil ?R =>
      let _ := match goal with _ => close_varlist lv end in
      constr:((lv, (@nil (PExpr Z))))
  | @cons ?R _ _ =>
      let R_ring := constr:(_ :> Ring (T:=R)) in
      list_reifyl R_ring lv lb
 end.

Ltac nsatz_guess_domain :=
  let eq := match goal with
            | |- @ex _ (fun e1 : _ => ?eq _ _ ) => eq
            | |- ?eq _ _ => eq
            end
  in
  let di :=
    lazymatch
      open_constr:(ltac:(typeclasses eauto):Integral_domain (ring_eq:=eq))
    with?di => di end
  in
  let __ := match di with _ => assert_fails (is_evar di) end in
  di.

Lemma efactor:
  forall A B P,  (exists x : A * B, P (fst x) (snd x)) -> (exists x : A, exists y: B, P x y).
Proof.
  intros A B P [x H]. eauto.
Qed.

Ltac ensatz_default info :=
  intros;
  repeat apply efactor;
  let di := nsatz_guess_domain in
  let r := lazymatch type of di with Integral_domain(R:=?r) => r end in
  let cr := lazymatch type of di with Integral_domain(Rcr:=?cr) => cr end in
  match goal with
  | |- @eq ?R ?E1 ?E2 =>
      match Eensatz_solve.Reifi.reify_goal with
      | (?lvar, ?x, ?v) =>
          let b := eval cbv delta [List.last] iota beta match
                       in (List.last x (PEc 0%Z))
          in
          let b := constr: (PEopp b) in
          let l := constr: (List.removelast x) in
          let n := eval compute in (List.length l) in
          repeat NsatzTactic.equalities_to_goal cr;
          match goal with
            |- ?g =>
              let lb := Eensatz_solve.hterm R g in
              intros;
              match reify_h lvar lb with
              | (?fv, ?le) =>
                let l := constr: (List.rev_append le l) in
                let le := constr: (b :: l) in
                let lpol := eval compute in le in
                match lpol with
                | ?p2::?lp2 => Eensatz_solve.ensatz_solve R p2 lp2 n fv v info
                | ?g => idtac "polynomial not in the ideal"
                end
              end
            end
           end
  | |- @ex _ (fun e1 : _ => @eq ?R (@?P1 e1) (@?P2 e1)) =>
      match Ensatz_solve.Reifi.reify_goal with
      | (?lvar, (fun _: _ => ?x)) =>
          let b :=
            eval cbv delta [List.last] iota beta match
                in (List.last x (PEc 0%Z))
          in
          let b := constr: (PEopp b) in
          let l := constr: (List.removelast x) in
          let n := eval compute in (List.length l) in
          repeat NsatzTactic.equalities_to_goal cr;
          match goal with
           |- ?g =>
             let lb := Ensatz_solve.hterm R g in
             intros;
             match reify_h lvar lb with
             | (?fv, ?le) =>
                let l := constr: (List.rev_append le l) in
                let le := constr: (b :: l) in
                let lpol := eval compute in le in
                match lpol with
                | ?p2::?lp2 => Ensatz_solve.ensatz_solve cr R p2 lp2 n fv info
                 | ?g => idtac "polynomial not in the ideal"
                 end
             end
        end
    end
  end.

Tactic Notation "ensatz" := ensatz_default 1%Z.

Tactic Notation "ensatz" "with"
 "strategy" ":=" constr(info) :=
  ensatz_default info.
