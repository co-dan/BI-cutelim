From Coq Require Import ssreflect.
From bunched.algebra Require Import bi.
From stdpp Require Import prelude.
From bunched Require Import bunches formula.


(** * Interpretation of BI intro the associated algebras *)

Section interp.
  Variable (PROP : bi).
  Notation bunch := (@bunch formula).
  Notation bunch_ctx := (@bunch_ctx formula).
  Implicit Types (A B C : PROP).
  Implicit Type Δ : bunch.
  Implicit Type Π : bunch_ctx.
  Implicit Type ψ ϕ χ : formula.

  (* Assume an interpretation of atomic formulas *)
  Variable (s : atom → PROP).

  Fixpoint formula_interp (ϕ : formula) : PROP :=
    match ϕ with
    | TOP => True
    | EMP => emp
    | BOT => False
    | ATOM a => s a
    | CONJ ϕ ψ => formula_interp ϕ ∧ formula_interp ψ
    | DISJ ϕ ψ => formula_interp ϕ ∨ formula_interp ψ
    | SEP ϕ ψ => formula_interp ϕ ∗ formula_interp ψ
    | IMPL ϕ ψ => formula_interp ϕ → formula_interp ψ
    | WAND ϕ ψ => formula_interp ϕ -∗ formula_interp ψ
    end%I.

  Notation bunch_interp := (bunch_interp formula_interp).

  Lemma bunch_interp_collapse Δ :
    bunch_interp Δ = formula_interp (collapse Δ).
  Proof.
    induction Δ as [ϕ|sp|sp Δ1 IH1 Δ2 IH2]; try destruct sp; simpl; eauto.
    - by rewrite IH1 IH2.
    - by rewrite IH1 IH2.
  Qed.

  Definition seq_interp Δ ϕ : Prop :=
    (bunch_interp Δ ⊢ formula_interp ϕ).

  Global Instance seq_interp_proper : Proper ((≡) ==> (=) ==> (≡)) seq_interp.
  Proof.
    intros Δ1 Δ2 HΔ ϕ ? <-. rewrite /seq_interp /=.
    split; rewrite -HΔ; eauto.
  Qed.

End interp.

Arguments formula_interp {_} _ _.
Arguments seq_interp {_} _ _ _.
