(* Bunched terms *)
From Equations Require Import Equations.
From Coq Require Import ssreflect.
From stdpp Require Import prelude gmap fin_sets.
From iris_mod.bi Require Import bi.
From bunched Require Import syntax.

(** * Bunched terms *)
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

Fixpoint bterm_alg_act {PROP : bi} `{!EqDecision V,!Countable V}
         (T : bterm V) (Xs : V → PROP) : PROP :=
  match T with
  | Var v => Xs v
  | TComma T1 T2 => bterm_alg_act T1 Xs ∗ bterm_alg_act T2 Xs
  end%I.

(** A semimorphism between BI algebras is a function that preserves ∗ and ∧ *)
Class SemiMorph {A B : bi} (f : A → B) :=
  { smor_sep (X Y : A) : (f X ∗ f Y)%I ≡ (f (X ∗ Y))%I; }.

Lemma bterm_fmap_compose {A B C} (f : A → B) (g : B → C) (T : bterm A) :
  (g ∘ f) <$> T = g <$> (f <$> T).
Proof.
  induction T; simpl; auto.
  rewrite IHT1 IHT2 //.
Qed.

Lemma bterm_ctx_act_fv `{!EqDecision V,!Countable V} (T : bterm V) Δs Γs :
  (∀ i : V, i ∈ term_fv T → Δs i = Γs i) →
  bterm_ctx_act T Δs = bterm_ctx_act T Γs.
Proof.
  induction T; simp term_fv ; simpl.
  - set_solver.
  - set_unfold. intros H.
    rewrite IHT1; eauto. rewrite IHT2; eauto.
Qed.

Lemma bterm_morph_commute {A B : bi} `{!EqDecision V, !Countable V}
      (T : bterm V) (Xs : V → A) (f : A → B) `{!SemiMorph f}:
  f (bterm_alg_act (PROP:=A) T Xs) ≡ bterm_alg_act (PROP:=B) T (f ∘ Xs).
Proof.
  induction T; simpl; first reflexivity.
  rewrite -IHT1 -IHT2. by rewrite smor_sep.
Qed.

