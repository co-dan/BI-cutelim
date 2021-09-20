From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From bunched.algebra Require Import bi.
From bunched Require Import seqcalc_s4.

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

  Definition bunch_ctx_item_interp (C : bunch_ctx_item) : PROP → PROP :=
    λ P, match C with
         | CtxCommaL Δ => P ∗ bunch_interp Δ
         | CtxCommaR Δ => bunch_interp Δ ∗ P
         | CtxSemicL Δ => P ∧ bunch_interp Δ
         | CtxSemicR Δ => bunch_interp Δ ∧ P
         end%I.

  Definition bunch_ctx_interp Π : PROP → PROP :=
    λ P, foldl (flip bunch_ctx_item_interp) P Π.

  Lemma bunch_ctx_interp_cons F Π A :
    bunch_ctx_interp (F::Π) A = bunch_ctx_interp Π (bunch_ctx_item_interp F A).
  Proof. reflexivity. Qed.

  Global Instance bunch_ctx_interp_proper Π : Proper ((≡) ==> (≡)) (bunch_ctx_interp Π).
  Proof.
    induction Π as [|F Π]=>X Y HXY.
    - simpl; auto.
    - simpl.
      eapply IHΠ.
      destruct F; solve_proper.
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

  Lemma bunch_interp_box Δ :
    bunch_interp (bunch_map BOX Δ) ⊢ box (bunch_interp Δ).
  Proof.
    induction Δ; simpl; eauto.
    - apply bi_box_true.
    - apply bi_box_emp.
    - rewrite IHΔ1 IHΔ2. apply bi_box_sep.
    - rewrite IHΔ1 IHΔ2. apply bi_box_conj.
  Qed.
  Lemma bunch_interp_box_idem Δ :
    bunch_interp (bunch_map BOX Δ) ⊢ bunch_interp (bunch_map BOX (bunch_map BOX Δ)).
  Proof.
    induction Δ; simpl; eauto.
    - apply bi_box_idem.
    - by rewrite IHΔ1 IHΔ2.
    - by rewrite IHΔ1 IHΔ2.
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
      destruct C; simpl; apply bunch_interp_fill_mono; simpl.
      all: by rewrite ?left_absorb ?right_absorb.
    - apply bi.True_intro.
    - by rewrite IHproves1 IHproves2.
    - by apply bi.or_intro_l.
    - by apply bi.or_intro_r.
    - revert IHproves1 IHproves2. clear.
      revert ϕ ψ.
      induction Π as [|F Π] => /= ϕ ψ IH1 IH2.
      { apply bi.or_elim; eauto. }
      destruct F; simpl; simpl in IH1, IH2;
      rewrite bunch_ctx_interp_decomp;
      cbn[bunch_interp formula_interp].
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
