From Coq Require Import ssreflect.
From stdpp Require Import prelude gmap fin_sets.
From bunched.algebra Require Import bi.
From bunched Require Import bunches.

(** * Formulas *)
Definition atom := nat.

(** ** Formulas and bunches *)
Inductive formula : Type :=
| TOP
| EMP
| BOT
| ATOM (A : atom)
| CONJ (ϕ ψ : formula)
| DISJ (ϕ ψ : formula)
| SEP (ϕ ψ : formula)
| IMPL (ϕ ψ : formula)
| WAND (ϕ ψ : formula)
| BOX (ϕ : formula)
.

(** "Collapse" internalizes the bunch as a formula. *)
Fixpoint collapse (Δ : @bunch formula) : formula :=
  match Δ with
  | frml ϕ => ϕ
  | ∅ₐ => TOP
  | ∅ₘ => EMP
  | Δ ,, Δ' => SEP (collapse Δ) (collapse Δ')
  | Δ ;, Δ' => CONJ (collapse Δ) (collapse Δ')
  end%B.

Inductive collapse_gr : @bunch formula → formula → Prop :=
| collapse_frml ϕ : collapse_gr (frml ϕ) ϕ
| collapse_top : collapse_gr ∅ₐ%B TOP
| collapse_emp : collapse_gr ∅ₘ%B EMP
| collapse_sep Δ1 Δ2 ϕ1 ϕ2 :
  collapse_gr Δ1 ϕ1 →
  collapse_gr Δ2 ϕ2 →
  collapse_gr (Δ1 ,, Δ2)%B (SEP ϕ1 ϕ2)
| collapse_conj Δ1 Δ2 ϕ1 ϕ2 :
  collapse_gr Δ1 ϕ1 →
  collapse_gr Δ2 ϕ2 →
  collapse_gr (Δ1 ;, Δ2)%B (CONJ ϕ1 ϕ2)
.

Lemma collapse_gr_sound Δ : collapse_gr Δ (collapse Δ).
Proof. induction Δ; simpl; try destruct s; try by econstructor. Qed.

Lemma collapse_gr_complete Δ ϕ : collapse_gr Δ ϕ → collapse Δ = ϕ.
Proof. induction 1; simpl; subst; eauto. Qed.

