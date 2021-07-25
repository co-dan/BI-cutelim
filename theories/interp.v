From Coq Require Import ssreflect.
From iris_mod.bi Require Import bi.
From stdpp Require Import prelude.
From bunched Require Import syntax.


(** * Interpretation of BI intro the associated algebras *)

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

  Program Definition bunch_ctx_item_interp (F : bunch_ctx_item) : PROP → PROP :=
    λ P, match F with
        | CtxCommaL Δ => P ∗ bunch_interp Δ
        | CtxCommaR Δ => bunch_interp Δ ∗ P
        | CtxSemicL Δ => P ∧ bunch_interp Δ
        | CtxSemicR Δ => bunch_interp Δ ∧ P
        end%I.

  Program Definition bunch_ctx_interp Π : PROP → PROP :=
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

  Lemma bunch_ctx_interp_exist Π {I} (P : I → PROP) :
    bunch_ctx_interp Π (∃ (i : I), P i : PROP)%I ≡
                     (∃ i, bunch_ctx_interp Π (P i))%I.
  Proof.
    revert P. induction Π as [|F Π]=>P.
    { simpl. reflexivity. }
    rewrite bunch_ctx_interp_cons.
    Opaque bunch_ctx_interp.
    destruct F; simpl.
    + rewrite bi.sep_exist_r.
      apply (IHΠ (λ i, P i ∗ bunch_interp Δ2)%I).
    + rewrite bi.sep_exist_l.
      apply (IHΠ (λ i, bunch_interp Δ1 ∗ P i)%I).
    + rewrite bi.and_exist_r.
      apply (IHΠ (λ i, P i ∧ bunch_interp Δ2)%I).
    + rewrite bi.and_exist_l.
      apply (IHΠ (λ i, bunch_interp Δ1 ∧ P i)%I).
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

  Global Instance bunch_ctx_interp_mono Π : Proper ((⊢) ==> (⊢)) (bunch_ctx_interp Π).
  Proof.
    induction Π as [|F Π]=>P1 P2 HP; first by simpl; auto.
    rewrite !bunch_ctx_interp_cons.
    apply IHΠ.
    destruct F; simpl; f_equiv; eauto.
  Qed.

  Global Instance seq_interp_proper : Proper ((≡) ==> (=) ==> (≡)) seq_interp.
  Proof.
    intros Δ1 Δ2 HΔ ϕ ? <-. rewrite /seq_interp /=.
    split; rewrite -HΔ; eauto.
  Qed.

End interp.
