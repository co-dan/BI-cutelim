From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From iris_mod.bi Require Import bi.
From bunched Require Import seqcalc.

(** * Interpretation of the sequent calculus in an arbitrary BI. *)

Section interp.

  Variable (PROP : bi).

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
    | SEP ϕ ψ => formula_interp ϕ ∗ formula_interp ψ
    | IMPL ϕ ψ => formula_interp ϕ → formula_interp ψ
    | WAND ϕ ψ => formula_interp ϕ -∗ formula_interp ψ
    end%I.

  Fixpoint bunch_interp (Δ : bunch) : PROP :=
    match Δ with
    | frml ϕ => formula_interp ϕ
    | top => True
    | empty => emp
    | (Δ ,, Δ')%B => bunch_interp Δ ∗ bunch_interp Δ'
    | (Δ ;, Δ')%B => bunch_interp Δ ∧ bunch_interp Δ'
    end%I.

  Lemma bunch_interp_collapse Δ :
    bunch_interp Δ ≡ formula_interp (collapse Δ).
  Proof.
    induction Δ; simpl; eauto.
    - by rewrite IHΔ1 IHΔ2.
    - by rewrite IHΔ1 IHΔ2.
  Qed.

  Definition seq_interp Δ ϕ : Prop :=
    (bunch_interp Δ ⊢ formula_interp ϕ).

  Program Definition bunch_ctx_item_interp (C : bunch_ctx_item) : PROP -n> PROP :=
    λne P, match C with
           | CtxCommaL Δ => P ∗ bunch_interp Δ
           | CtxCommaR Δ => bunch_interp Δ ∗ P
           | CtxSemicL Δ => P ∧ bunch_interp Δ
           | CtxSemicR Δ => bunch_interp Δ ∧ P
           end%I.
  Next Obligation. intros C. destruct C; solve_proper. Qed.

  Program Definition bunch_ctx_interp Π : PROP -n> PROP :=
    λne P, foldl (flip bunch_ctx_item_interp) P Π.
  Next Obligation.
    intros Π. induction Π.
    - apply _.
    - intros n P P' HP.
      cbn[foldl].
      eapply IHΠ.
      cbn[flip]. by eapply bunch_ctx_item_interp.
  Qed.

  Lemma bunch_ctx_interp_decomp Π Δ :
    bunch_interp (fill Π Δ) ≡ bunch_ctx_interp Π (bunch_interp Δ).
  Proof.
    revert Δ. induction Π as [|C Π IH]=>Δ; first by reflexivity.
    apply bi.equiv_entails_2.
    - destruct C; simpl; by rewrite IH.
    - destruct C; simpl; by rewrite IH.
  Qed.

  Lemma bunch_interp_fill_item_mono (C : bunch_ctx_item) Δ Δ' :
    (bunch_interp Δ ⊢ bunch_interp Δ') →
    bunch_interp (fill_item C Δ) ⊢ bunch_interp (fill_item C Δ').
  Proof.
    intros H1.
    induction C as [ ? | ? | ? | ? ]; simpl; by rewrite H1.
  Qed.

  Lemma bunch_interp_fill_mono Π Δ Δ' :
    (bunch_interp Δ ⊢ bunch_interp Δ') →
    bunch_interp (fill Π Δ) ⊢ bunch_interp (fill Π Δ').
  Proof.
    revert Δ Δ'.
    induction Π as [|C Π IH]=> Δ Δ' H1; eauto.
    simpl. apply IH.
    by apply bunch_interp_fill_item_mono.
  Qed.

  Global Instance bunch_interp_proper : Proper ((≡) ==> (≡)) bunch_interp.
  Proof.
    intros Δ1 Δ2. induction 1; eauto.
    - etrans; eassumption.
    - apply bi.equiv_entails_2.
      + apply bunch_interp_fill_mono; eauto.
        by apply bi.equiv_entails_1_1.
      + apply bunch_interp_fill_mono; eauto.
        by apply bi.equiv_entails_1_2.
    - simpl. by rewrite left_id.
    - simpl. by rewrite comm.
    - simpl. by rewrite assoc.
    - simpl. by rewrite left_id.
    - simpl. by rewrite comm.
    - simpl. by rewrite assoc.
  Qed.

  Global Instance seq_interp_proper : Proper ((≡) ==> (=) ==> (≡)) seq_interp.
  Proof.
    intros Δ1 Δ2 HΔ ϕ ? <-. rewrite /seq_interp /=.
    split; rewrite -HΔ; eauto.
  Qed.

  Theorem seq_interp_sound Δ ϕ : (Δ ⊢ᴮ ϕ) → seq_interp Δ ϕ.
  Proof.
    induction 1; unfold seq_interp; simpl; eauto; try rewrite -IHproves.
    all: try by apply bunch_interp_fill_mono.
    - by rewrite -H.
    - apply bunch_interp_fill_mono; simpl.
      by rewrite bi.and_elim_l.
    - apply bunch_interp_fill_mono; simpl.
      apply bi.and_intro; eauto.
    - by rewrite IHproves1 IHproves2.
    - by apply bi.wand_intro_r.
    - rewrite -IHproves2.
      apply bunch_interp_fill_mono; simpl.
      rewrite IHproves1. apply bi.wand_elim_r.
    - induction C as [|C Π IH]; simpl.
      { apply bi.False_elim. }
      rewrite -IH.
      destruct C; simpl; apply bunch_interp_fill_mono; simpl.
      all: by rewrite ?left_absorb ?right_absorb.
    - apply bi.True_intro.
    - by rewrite IHproves1 IHproves2.
    - by apply bi.impl_intro_r.
    - rewrite -IHproves2.
      apply bunch_interp_fill_mono; simpl.
      rewrite IHproves1. apply bi.impl_elim_r.
  Qed.

End interp.
