From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From stdpp Require Import gmap fin_sets.
From iris_mod.bi Require Import bi .
From bunched Require Import seqcalc interp cutelim.
From Equations Require Import Equations.
Set Transparent Obligations.

(* Bunched terms *)
Inductive bterm (var : Type) : Type :=
| Var (x : var)
| TComma (T1 T2 : bterm var)
.
Arguments Var {_} x.
Arguments TComma {_} T1 T2.


Global Instance bterm_fmap : FMap bterm :=
  fix go _ _ f T { struct T } := let _ : FMap _ := go in
  match T with
  | Var x => Var (f x)
  | TComma T1 T2 => TComma (f <$> T1) (f <$> T2)
  end.

Lemma bterm_fmap_compose {A B C} (f : A → B) (g : B → C) (T : bterm A) :
  (g ∘ f) <$> T = g <$> (f <$> T).
Proof.
  induction T; simpl; auto.
  rewrite IHT1 IHT2 //.
Qed.


Equations term_fv `{!EqDecision V,!Countable V} (T : bterm V) : gset V :=
  term_fv (Var x) := {[ x ]};
  term_fv (TComma T1 T2) := term_fv T1 ∪ term_fv T2;
.

Equations linear_bterm `{!EqDecision V,!Countable V}
  (T : bterm V) : Prop :=
  linear_bterm (Var x) := True;
  linear_bterm (TComma T1 T2) :=
    term_fv T1 ## term_fv T2 ∧
    linear_bterm T1 ∧ linear_bterm T2.

Fixpoint bterm_ctx_act `{!EqDecision V,!Countable V}
         (T : bterm V) (Δs : V → bunch) : bunch :=
  match T with
  | Var v => Δs v
  | TComma T1 T2 => bterm_ctx_act T1 Δs,, bterm_ctx_act T2 Δs
  end%B.

Lemma bterm_ctx_act_fv `{!EqDecision V,!Countable V} (T : bterm V) Δs Γs :
  (∀ i : V, i ∈ term_fv T → Δs i = Γs i) →
  bterm_ctx_act T Δs = bterm_ctx_act T Γs.
Proof.
  induction T; simp term_fv ; simpl.
  - set_solver.
  - set_unfold. intros H.
    rewrite IHT1; eauto. rewrite IHT2; eauto.
Qed.

Fixpoint bterm_alg_act {PROP : bi} `{!EqDecision V,!Countable V}
         (T : bterm V) (Xs : V → PROP) : PROP :=
  match T with
  | Var v => Xs v
  | TComma T1 T2 => bterm_alg_act T1 Xs ∗ bterm_alg_act T2 Xs
  end%I.

Class SemiMorph {A B : bi} (f : A → B) :=
  { smor_sep (X Y : A) : (f X ∗ f Y)%I ≡ (f (X ∗ Y))%I; }.

Lemma bterm_morph_commute {A B : bi} `{!EqDecision V, !Countable V}
      (T : bterm V) (Xs : V → A) (f : A → B) `{!SemiMorph f}:
  f (bterm_alg_act (PROP:=A) T Xs) ≡ bterm_alg_act (PROP:=B) T (f ∘ Xs).
Proof.
  induction T; simpl; first reflexivity.
  rewrite -IHT1 -IHT2. by rewrite smor_sep.
Qed.

Import PB.
Import Cl.
Definition interp_C := Cl.inner_interp.
Definition interp_PB := formula_interp PB.PB_alg (λ x, Cl.Fint (ATOM x)).

Instance cl_semimorph : SemiMorph (cl' : PB_alg → C_alg).
Proof.
  split.
  - intros X Y.
    rewrite (cl_sep X Y).
    reflexivity.
Qed.

Instance ElemOf_C : ElemOf bunch C := λ a X, X a.
Instance ElemOf_PB : ElemOf bunch PB := λ a X, X a.

Lemma bterm_C_refl `{!EqDecision V, !Countable V}
      (T : bterm V) (Xs : V → C_alg) :
  ∀ (Δs : V → bunch),
    (forall (i : V), (Δs i) ∈ (Xs i)) ->
    bterm_ctx_act T Δs ∈ bterm_alg_act T Xs.
Proof.
  intros Δs HΔ.
  induction T; simpl.
  - apply HΔ.
  - apply cl_unit. do 2 eexists.
    repeat split; last reflexivity.
    + apply IHT1.    + apply IHT2.
Qed.

Definition ii (X : C_alg) : PB_alg := X.


Lemma blinterm_alg_desc `{!EqDecision V, !Countable V}
      (T : bterm V) (TL : linear_bterm T)
      (Xs : V → C_alg) (Δ : bunch) :
  bterm_alg_act (PROP:=PB_alg) T Xs Δ →
  ∃ (Δs : V → bunch),
    (forall (i : V), (Δs i) ∈ (Xs i)) ∧
    Δ ≡ bterm_ctx_act T Δs.
Proof.
  revert Δ Xs. induction T=>Δ Xs /=.
  - unfold ii. intros HXs.
    exists (λ (i : V),
                if decide (i = x) then Δ
                else frml BOT).
    rewrite decide_True//. split; auto.
    intros i. case_decide; simplify_eq/=; auto.
    admit.
  - intros (Δ1 & Δ2 & H1 & H2 & Heq).
    simp linear_bterm in TL.
    destruct TL as (Hfv & HL1 & HL2).
    destruct (IHT1 HL1 _ _ H1) as (Δs1 & HΔs1 & HDs1eq).
    destruct (IHT2 HL2 _ _ H2) as (Δs2 & HΔs2 & HDs2eq).
    pose (Δs := λ (x : V),
                if decide (x ∈ term_fv T1) then Δs1 x
                else Δs2 x).
    exists Δs. split.
    + intros i. unfold Δs.
      case_decide; auto.
    + assert (bterm_ctx_act T1 Δs1 = bterm_ctx_act T1 Δs) as <-.
      { apply bterm_ctx_act_fv.
        unfold Δs. intros i Hi.
        case_decide; auto. exfalso. auto. }
      assert (bterm_ctx_act T2 Δs2 = bterm_ctx_act T2 Δs) as <-.
      { apply bterm_ctx_act_fv.
        unfold Δs. intros i Hi.
        case_decide; auto. exfalso.
        revert Hfv Hi. set_unfold.
        naive_solver. }
      rewrite Heq. by f_equiv.
Admitted.
