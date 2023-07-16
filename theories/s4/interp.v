From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From bunched.algebra Require Import bi.
From bunched Require Import bunches.
From bunched.s4 Require Import formula seqcalc.

(** * Interpretation of the sequent calculus in an arbitrary BI. *)

Class BiBox (PROP : bi) (box : PROP → PROP) :=
  { bi_box_mono P Q : (P ⊢ Q) → (box P ⊢ box Q);
    bi_box_elim P : box P ⊢ P;
    bi_box_idem P : box P ⊢ box (box P);
    bi_box_conj P Q : (box P) ∧ (box Q) ⊢ box (P ∧ Q);
    bi_box_sep P Q : (box P) ∗ (box Q) ⊢ box (P ∗ Q);
    bi_box_true : True ⊢ box True;
    bi_box_emp : emp ⊢ box emp;
  }.
Section interp.

  Variable (PROP : bi).
  Variable (box : PROP → PROP).
  Context `{!BiBox PROP box}.
  Notation bunch := (@bunch formula).
  Notation bunch_ctx := (@bunch_ctx formula).

  Notation "□ A" := (box A) : bi_scope.

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
    | DISJ ϕ ψ => formula_interp ϕ ∨ formula_interp ψ
    | CONJ ϕ ψ => formula_interp ϕ ∧ formula_interp ψ
    | SEP ϕ ψ => formula_interp ϕ ∗ formula_interp ψ
    | IMPL ϕ ψ => formula_interp ϕ → formula_interp ψ
    | WAND ϕ ψ => formula_interp ϕ -∗ formula_interp ψ
    | BOX ϕ => □ (formula_interp ϕ)
    end%I.

  Notation bunch_interp := (bunch_interp formula_interp).

  Lemma bunch_interp_collapse Δ :
    bunch_interp Δ = formula_interp (collapse Δ).
  Proof.
    induction Δ as [ϕ|sp|sp Δ1 IH1 Δ2 IH2]; try destruct sp; simpl; eauto.
    - by rewrite IH1 IH2.
    - by rewrite IH1 IH2.
  Qed.

  Lemma bunch_interp_box Δ :
    bunch_interp (BOX <$> Δ) ⊢ □ (bunch_interp Δ).
  Proof.
    induction Δ as [ϕ|sp|sp Δ1 IH1 Δ2 IH2]; try destruct sp; simpl; eauto.
    - apply bi_box_emp.
    - apply bi_box_true.
    - rewrite IH1 IH2. apply bi_box_sep.
    - rewrite IH1 IH2. apply bi_box_conj.
  Qed.

  Lemma bunch_interp_box_idem (Δ : bunch) :
    bunch_interp (BOX <$> Δ) ⊢ bunch_interp (BOX <$> (BOX <$> Δ)).
  Proof.
    induction Δ as [ϕ|sp|sp Δ1 IH1 Δ2 IH2]; try destruct sp; simpl; eauto.
    - apply bi_box_idem.
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

  Theorem seq_interp_sound Δ ϕ : (Δ ⊢ᴮ ϕ) → seq_interp Δ ϕ.
  Proof.
    induction 1; unfold seq_interp; simpl; eauto; try rewrite -IHproves.
    all: try by apply bunch_interp_fill_mono.
    - by rewrite -H.
    - apply bunch_interp_fill_mono; simpl.
      by rewrite bi.and_elim_l.
    - apply bunch_interp_fill_mono; simpl.
      apply bi.and_intro; eauto.
    - apply bunch_interp_fill_mono; simpl.
      apply bi_box_elim.
    - rewrite bunch_interp_box_idem bunch_interp_box.
      apply bi_box_mono, IHproves.
    - by rewrite IHproves1 IHproves2.
    - by apply bi.wand_intro_r.
    - rewrite -IHproves2.
      apply bunch_interp_fill_mono; simpl.
      rewrite IHproves1. apply bi.wand_elim_r.
    - induction C as [|C Π IH]; simpl.
      { apply bi.False_elim. }
      rewrite -IH.
      destruct C as [[] ?|  [] ?]; simpl; apply bunch_interp_fill_mono; simpl.
      all: by rewrite ?left_absorb ?right_absorb.
    - apply bi.True_intro.
    - by rewrite IHproves1 IHproves2.
    - by apply bi.or_intro_l.
    - by apply bi.or_intro_r.
    - revert IHproves1 IHproves2. clear.
      revert ϕ ψ.
      induction Π as [|F Π] => /= ϕ ψ IH1 IH2.
      { apply bi.or_elim; eauto. }
      destruct F as [[] ? IH1|[] ? IH2]; simpl; simpl in IH1, IH2;
      rewrite bunch_ctx_interp_decomp;
      cbn[sep_interp bunch_interp formula_interp].
      + rewrite bi.sep_or_r.
        unfold seq_interp in *.
        etrans.
        2:{ eapply (IHΠ (SEP ϕ (collapse Δ2)) (SEP ψ (collapse Δ2))).
            - rewrite -IH1.
              apply bunch_interp_fill_mono; simpl.
              by rewrite bunch_interp_collapse.
            - rewrite -IH2.
              apply bunch_interp_fill_mono; simpl.
              by rewrite bunch_interp_collapse. }
        rewrite bunch_ctx_interp_decomp.
        cbn[bunch_interp formula_interp].
        by rewrite bunch_interp_collapse.
      + rewrite bi.and_or_r.
        unfold seq_interp in *.
        etrans.
        2:{ eapply (IHΠ (CONJ ϕ (collapse Δ2)) (CONJ ψ (collapse Δ2))).
            - rewrite -IH1.
              apply bunch_interp_fill_mono; simpl.
              by rewrite bunch_interp_collapse.
            - rewrite -IH2.
              apply bunch_interp_fill_mono; simpl.
              by rewrite bunch_interp_collapse. }
        rewrite bunch_ctx_interp_decomp.
        cbn[bunch_interp formula_interp].
        by rewrite bunch_interp_collapse.
      + rewrite bi.sep_or_l.
        unfold seq_interp in *.
        etrans.
        2:{ eapply (IHΠ (SEP (collapse Δ1) ϕ) (SEP (collapse Δ1) ψ)).
            - rewrite -IH1.
              apply bunch_interp_fill_mono; simpl.
              by rewrite bunch_interp_collapse.
            - rewrite -IH2.
              apply bunch_interp_fill_mono; simpl.
              by rewrite bunch_interp_collapse. }
        rewrite bunch_ctx_interp_decomp.
        cbn[bunch_interp formula_interp].
        by rewrite bunch_interp_collapse.
      + rewrite bi.and_or_l.
        unfold seq_interp in *.
        etrans.
        2:{ eapply (IHΠ (CONJ (collapse Δ1) ϕ) (CONJ (collapse Δ1) ψ)).
            - rewrite -IH1.
              apply bunch_interp_fill_mono; simpl.
              by rewrite bunch_interp_collapse.
            - rewrite -IH2.
              apply bunch_interp_fill_mono; simpl.
              by rewrite bunch_interp_collapse. }
        rewrite bunch_ctx_interp_decomp.
        cbn[bunch_interp formula_interp].
        by rewrite bunch_interp_collapse.
    - by apply bi.impl_intro_r.
    - rewrite -IHproves2.
      apply bunch_interp_fill_mono; simpl.
      rewrite IHproves1. apply bi.impl_elim_r.
  Qed.

End interp.
