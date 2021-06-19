(* Sequent calculus with upper bounds on proof size.
   Useful for doing induction on.

   The main purpose this file is to provide the inversion lemmas (at the very bottom of the file).
 *)
From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From iris_mod.bi Require Import bi.
From bunched Require Import seqcalc.

Reserved Notation "P ⊢ᴮ{ n } Q" (at level 99, n, Q at level 200, right associativity).
Reserved Notation "Δ =?{ n } Δ'" (at level 99, n at level 200).

Module bunchHeight.

  Implicit Type Δ : bunch.
  Implicit Type ψ ϕ : formula.

  (** ** Alternative formulation of bunch equivalences *)
  Inductive bunch_equiv : bunch → bunch → Prop :=
  | BE_cong C Δ1 Δ2 :
      Δ1 =? Δ2 →
      fill C Δ1 =? fill C Δ2
  | BE_comma_unit_l Δ :
      (empty ,, Δ)%B =? Δ
  | BE_comma_comm Δ1 Δ2 :
      (Δ1 ,, Δ2)%B =? (Δ2 ,, Δ1)%B
  | BE_comma_assoc Δ1 Δ2 Δ3 : (Δ1 ,, (Δ2 ,, Δ3))%B =? ((Δ1 ,, Δ2) ,, Δ3)%B
  | BE_semic_unit_l Δ : (top ;, Δ)%B =? Δ
  | BE_semic_comm Δ1 Δ2  : (Δ1 ;, Δ2)%B =? (Δ2 ;, Δ1)%B
  | BE_semic_assoc Δ1 Δ2 Δ3  : (Δ1 ;, (Δ2 ;, Δ3))%B =? ((Δ1 ;, Δ2) ;, Δ3)%B
  where "Δ =? Γ" := (bunch_equiv Δ%B Γ%B).

  Definition bunch_equiv_h := rtsc (bunch_equiv).

  (* TODO: prove rtsc_subrel and move to relations.v *)
  Lemma sc_subrel {A} (R1 R2 : relation A) x y :
    (∀ x1 x2, R1 x1 x2 → R2 x1 x2) →
    sc R1 x y → sc R2 x y.
  Proof.
    intros HR H1.
    destruct H1 as [H1 | H1]; by econstructor; apply HR.
  Qed.

  Lemma bunch_equiv_1 Δ Δ' :
    (Δ =? Δ') → (Δ ≡ Δ').
  Proof. induction 1; by econstructor; eauto. Qed.

  Lemma bunch_equiv_2 Δ Δ' :
    (Δ ≡ Δ') → (bunch_equiv_h Δ Δ').
  Proof.
    induction 1.
    all: try by (eapply rtsc_lr; econstructor).
    - unfold bunch_equiv_h. reflexivity.
    - by symmetry.
    - etrans; eauto.
    - eapply rtc_congruence; eauto.
      intros X Y. apply sc_congruence. clear X Y.
      intros X Y ?. by econstructor.
  Qed.

  Local Lemma bunch_equiv_fill_1 Δ C ϕ :
    fill C (frml ϕ) =? Δ →
    ∃ C', Δ = fill C' (frml ϕ) ∧ (∀ Δ, fill C' Δ ≡ fill C Δ).
  Proof.
    intros Heq.
    remember (fill C (frml ϕ)) as Y.
    revert C HeqY.
    induction Heq=>C' heqY; symmetry in heqY.
    + apply bunch_decomp_complete in heqY.
      apply bunch_decomp_ctx in heqY.
      destruct heqY as [H1 | H2].
      * destruct H1 as [C1 [HC0%bunch_decomp_correct HC]].
        destruct (IHHeq C1 HC0) as [C2 [HΔ1 HC2]].
        simplify_eq/=.
        exists (C2 ++ C). rewrite fill_app. split; first done.
        intros Δ. rewrite !fill_app HC2 //.
      * destruct H2 as (C1 & C2 & HC1 & HC2 & Hdec0).
        specialize (Hdec0 Δ2). apply bunch_decomp_correct in Hdec0.
        exists (C1 Δ2). split ; eauto.
        intros Δ. rewrite HC1.
        assert (Δ1 ≡ Δ2) as <-.
        { by apply bunch_equiv_1. }
        by rewrite HC2.
    + apply bunch_decomp_complete in heqY.
      inversion heqY; simplify_eq/=.
      { inversion H3. }
      apply bunch_decomp_correct in H3.
      exists Π. split; eauto.
      intros X. rewrite fill_app /= left_id //.
    + apply bunch_decomp_complete in heqY.
      inversion heqY; simplify_eq/=.
      * exists (Π ++ [CtxCommaR Δ2]). split.
        { rewrite fill_app/=.
          apply bunch_decomp_correct in H3.
          by rewrite H3. }
        intros Δ. rewrite !fill_app/=.
        by rewrite comm.
      * exists (Π ++ [CtxCommaL Δ1]). split.
        { rewrite fill_app/=.
          apply bunch_decomp_correct in H3.
          by rewrite H3. }
        intros Δ. rewrite !fill_app/=.
        by rewrite comm.
    + apply bunch_decomp_complete in heqY.
      inversion heqY; simplify_eq/=.
      * exists (Π ++ [CtxCommaL Δ2;CtxCommaL Δ3])%B. split.
        { rewrite fill_app/=.
          apply bunch_decomp_correct in H3.
          by rewrite H3. }
        intros Δ. rewrite !fill_app/=.
        by rewrite assoc.
      * inversion H3; simplify_eq/=.
        ** exists (Π0 ++ [CtxCommaR Δ1;CtxCommaL Δ3])%B. split.
           { rewrite fill_app/=.
             apply bunch_decomp_correct in H4.
               by rewrite H4. }
           intros Δ. rewrite !fill_app/=.
           by rewrite assoc.
        ** exists (Π0 ++ [CtxCommaR (Δ1,,Δ2)])%B. split.
           { simpl. rewrite fill_app/=.
             apply bunch_decomp_correct in H4.
             by rewrite H4. }
           intros Δ. rewrite !fill_app/=.
           by rewrite assoc.
    + apply bunch_decomp_complete in heqY.
      inversion heqY; simplify_eq/=.
      { inversion H3. }
      apply bunch_decomp_correct in H3.
      exists Π. split; eauto.
      intros X. rewrite fill_app /= left_id //.
    + apply bunch_decomp_complete in heqY.
      inversion heqY; simplify_eq/=.
      * exists (Π ++ [CtxSemicR Δ2]). split.
        { rewrite fill_app/=.
          apply bunch_decomp_correct in H3.
          by rewrite H3. }
        intros Δ. rewrite !fill_app/=.
        by rewrite comm.
      * exists (Π ++ [CtxSemicL Δ1]). split.
        { rewrite fill_app/=.
          apply bunch_decomp_correct in H3.
          by rewrite H3. }
        intros Δ. rewrite !fill_app/=.
        by rewrite comm.
    + apply bunch_decomp_complete in heqY.
      inversion heqY; simplify_eq/=.
      * exists (Π ++ [CtxSemicL Δ2;CtxSemicL Δ3])%B. split.
        { rewrite fill_app/=.
          apply bunch_decomp_correct in H3.
          by rewrite H3. }
        intros Δ. rewrite !fill_app/=.
        by rewrite assoc.
      * inversion H3; simplify_eq/=.
        ** exists (Π0 ++ [CtxSemicR Δ1;CtxSemicL Δ3])%B. split.
           { rewrite fill_app/=.
             apply bunch_decomp_correct in H4.
               by rewrite H4. }
           intros Δ. rewrite !fill_app/=.
           by rewrite assoc.
        ** exists (Π0 ++ [CtxSemicR (Δ1;,Δ2)])%B. split.
           { simpl. rewrite fill_app/=.
             apply bunch_decomp_correct in H4.
             by rewrite H4. }
           intros Δ. rewrite !fill_app/=.
           by rewrite assoc.
  Qed.

  Local Lemma bunch_equiv_fill_2 Δ C ϕ :
    Δ =? fill C (frml ϕ) →
    ∃ C', Δ = fill C' (frml ϕ) ∧ (∀ Δ, fill C' Δ ≡ fill C Δ).
  Proof.
    intros Heq.
    remember (fill C (frml ϕ)) as Y.
    revert C HeqY.
    induction Heq=>C' heqY; symmetry in heqY.
    + apply bunch_decomp_complete in heqY.
      apply bunch_decomp_ctx in heqY.
      destruct heqY as [H1 | H2].
      * destruct H1 as [C1 [HC0%bunch_decomp_correct HC]].
        destruct (IHHeq C1 HC0) as [C2 [HΔ1 HC2]].
        simplify_eq/=.
        exists (C2 ++ C). rewrite fill_app. split; first done.
        intros Δ. rewrite !fill_app HC2 //.
      * destruct H2 as (C1 & C2 & HC1 & HC2 & Hdec0).
        specialize (Hdec0 Δ1). apply bunch_decomp_correct in Hdec0.
        exists (C1 Δ1). split ; eauto.
        intros Δ. rewrite HC1.
        assert (Δ1 ≡ Δ2) as ->.
        { by apply bunch_equiv_1. }
        by rewrite HC2.
    + exists (C' ++ [CtxCommaR empty]). simpl; split.
      { rewrite fill_app /=. by rewrite heqY. }
      intros X; rewrite fill_app/=.
      by rewrite left_id.
    + apply bunch_decomp_complete in heqY.
      inversion heqY; simplify_eq/=.
      * exists (Π ++ [CtxCommaR Δ1]). split.
        { rewrite fill_app/=.
          apply bunch_decomp_correct in H3.
          by rewrite H3. }
        intros Δ. rewrite !fill_app/=.
        by rewrite comm.
      * exists (Π ++ [CtxCommaL Δ2]). split.
        { rewrite fill_app/=.
          apply bunch_decomp_correct in H3.
          by rewrite H3. }
        intros Δ. rewrite !fill_app/=.
        by rewrite comm.
    + apply bunch_decomp_complete in heqY.
      inversion heqY; simplify_eq/=.
      * inversion H3; simplify_eq/=.
        ** exists (Π0 ++ [CtxCommaL (Δ2 ,, Δ3)])%B. split.
           { rewrite fill_app/=.
             apply bunch_decomp_correct in H4.
               by rewrite H4. }
           intros Δ. rewrite !fill_app/=.
           by rewrite assoc.
        ** exists (Π0 ++ [CtxCommaL Δ3;CtxCommaR Δ1])%B. split.
           { simpl. rewrite fill_app/=.
             apply bunch_decomp_correct in H4.
             by rewrite H4. }
           intros Δ. rewrite !fill_app/=.
           by rewrite assoc.
      * exists (Π ++ [CtxCommaR Δ2;CtxCommaR Δ1])%B. split.
        { rewrite fill_app/=.
          apply bunch_decomp_correct in H3.
            by rewrite H3. }
           intros Δ. rewrite !fill_app/=.
           by rewrite assoc.
    + exists (C' ++ [CtxSemicR top]). simpl; split.
      { rewrite fill_app /=. by rewrite heqY. }
      intros X; rewrite fill_app/=.
      by rewrite left_id.
    + apply bunch_decomp_complete in heqY.
      inversion heqY; simplify_eq/=.
      * exists (Π ++ [CtxSemicR Δ1]). split.
        { rewrite fill_app/=.
          apply bunch_decomp_correct in H3.
          by rewrite H3. }
        intros Δ. rewrite !fill_app/=.
        by rewrite comm.
      * exists (Π ++ [CtxSemicL Δ2]). split.
        { rewrite fill_app/=.
          apply bunch_decomp_correct in H3.
          by rewrite H3. }
        intros Δ. rewrite !fill_app/=.
        by rewrite comm.
    + apply bunch_decomp_complete in heqY.
      inversion heqY; simplify_eq/=.
      * inversion H3; simplify_eq/=.
        ** exists (Π0 ++ [CtxSemicL (Δ2 ;, Δ3)])%B. split.
           { rewrite fill_app/=.
             apply bunch_decomp_correct in H4.
             by rewrite H4. }
           intros Δ. rewrite !fill_app/=.
           by rewrite assoc.
        ** exists (Π0 ++ [CtxSemicL Δ3;CtxSemicR Δ1])%B. split.
           { simpl. rewrite fill_app/=.
             apply bunch_decomp_correct in H4.
             by rewrite H4. }
           intros Δ. rewrite !fill_app/=.
           by rewrite assoc.
      * exists (Π ++ [CtxSemicR Δ2;CtxSemicR Δ1])%B. split.
        { rewrite fill_app/=.
          apply bunch_decomp_correct in H3.
            by rewrite H3. }
           intros Δ. rewrite !fill_app/=.
           by rewrite assoc.
  Qed.

  Lemma bunch_equiv_fill Δ C ϕ :
    Δ ≡ (fill C (frml ϕ)) →
    ∃ C', Δ = fill C' (frml ϕ) ∧ (∀ Δ, fill C' Δ ≡ fill C Δ).
  Proof.
    intros H%bunch_equiv_2.
    revert Δ H. eapply rtc_ind_l.
    { exists C. eauto. }
    intros X Y HXY HY. clear HY.
    intros (C0 & -> & HC0).
    destruct HXY as [HXY|HXY].
    - apply bunch_equiv_fill_2 in HXY.
      destruct HXY as (C' & -> & HC').
      eexists; split; eauto.
      intros ?. by rewrite HC' HC0.
    - apply bunch_equiv_fill_1 in HXY.
      destruct HXY as (C' & -> & HC').
      eexists; split; eauto.
      intros ?. by rewrite HC' HC0.
  Qed.

  (** * SEQUENT CALCULUS *)
  Polymorphic Inductive proves : bunch → formula → nat → Prop :=
    (* structural *)
  | BI_Higher Δ ϕ n : (Δ ⊢ᴮ{n} ϕ) → (Δ ⊢ᴮ{S n} ϕ)
  | BI_Axiom (a : atom) : frml (ATOM a) ⊢ᴮ{0} ATOM a
  | BI_Equiv Δ Δ' ϕ n :
      (Δ ≡ Δ') → (Δ ⊢ᴮ{n} ϕ) →
      Δ' ⊢ᴮ{S n} ϕ
  | BI_Weaken C Δ Δ' ϕ n : (fill C Δ ⊢ᴮ{n} ϕ) →
                         fill C (Δ ;, Δ') ⊢ᴮ{S n} ϕ
  | BI_Contr C Δ ϕ n : (fill C (Δ ;, Δ) ⊢ᴮ{n} ϕ) →
                     fill C Δ ⊢ᴮ{S n} ϕ
  (* | BI_Cut C Δ ϕ ψ : (Δ ⊢ᴮ ψ) → *)
  (*                    (fill C (frml ψ) ⊢ᴮ ϕ) → *)
  (*                    fill C Δ ⊢ᴮ ϕ *)
    (* multiplicatives *)
  | BI_Emp_R :
      empty ⊢ᴮ{0} EMP
  | BI_Emp_L C ϕ n :
      (fill C empty ⊢ᴮ{n} ϕ) →
      fill C (frml EMP) ⊢ᴮ{S n} ϕ
  | BI_Sep_R Δ Δ' ϕ ψ n m :
      (Δ ⊢ᴮ{n} ϕ) →
      (Δ' ⊢ᴮ{m} ψ) →
      Δ ,, Δ' ⊢ᴮ{S (n `max` m)} SEP ϕ ψ
  | BI_Sep_L C ϕ ψ χ n :
      (fill C (frml ϕ ,, frml ψ) ⊢ᴮ{n} χ) →
      fill C (frml (SEP ϕ ψ)) ⊢ᴮ{S n} χ
  | BI_Wand_R Δ ϕ ψ n :
      (Δ ,, frml ϕ ⊢ᴮ{n} ψ) →
      Δ  ⊢ᴮ{S n} WAND ϕ ψ
  | BI_Wand_L C Δ ϕ ψ χ n m :
      (Δ ⊢ᴮ{n} ϕ) →
      (fill C (frml ψ) ⊢ᴮ{m} χ) →
      fill C (Δ ,, frml (WAND ϕ ψ)) ⊢ᴮ{S (n `max` m)} χ
    (* additives *)
  | BI_False_L C ϕ :
      fill C (frml BOT) ⊢ᴮ{0} ϕ
  | BI_True_R Δ :
      Δ ⊢ᴮ{0} TOP
  | BI_True_L C ϕ n :
      (fill C top ⊢ᴮ{n} ϕ) →
      fill C (frml TOP) ⊢ᴮ{S n} ϕ
  | BI_Conj_R Δ Δ' ϕ ψ n m :
      (Δ ⊢ᴮ{n} ϕ) →
      (Δ' ⊢ᴮ{m} ψ) →
      Δ ;, Δ' ⊢ᴮ{S (n `max` m)} CONJ ϕ ψ
  | BI_Conj_L C ϕ ψ χ n :
      (fill C (frml ϕ ;, frml ψ) ⊢ᴮ{n} χ) →
      fill C (frml (CONJ ϕ ψ)) ⊢ᴮ{S n} χ
  | BI_Impl_R Δ ϕ ψ n :
      (Δ ;, frml ϕ ⊢ᴮ{n} ψ) →
      Δ  ⊢ᴮ{S n} IMPL ϕ ψ
  | BI_Impl_L C Δ ϕ ψ χ n m:
      (Δ ⊢ᴮ{n} ϕ) →
      (fill C (frml ψ) ⊢ᴮ{m} χ) →
      fill C (Δ ;, frml (IMPL ϕ ψ)) ⊢ᴮ{S (n `max` m)} χ
  where "Δ ⊢ᴮ{ n } ϕ" := (proves Δ%B ϕ%B n).

  Lemma provesN_proves n Δ ϕ :
    (Δ ⊢ᴮ{ n } ϕ) → Δ ⊢ᴮ ϕ.
  Proof.
    induction 1; eauto.
    by econstructor; eauto.
    by econstructor; eauto.
    by econstructor; eauto.
    by econstructor; eauto.
    by econstructor; eauto.
    by econstructor; eauto.
    by econstructor; eauto.
    by econstructor; eauto.
    by econstructor; eauto.
    by econstructor; eauto.
    by econstructor; eauto.
    by econstructor; eauto.
    by econstructor; eauto.
    by econstructor; eauto.
    by econstructor; eauto.
    by econstructor; eauto.
    by econstructor; eauto.
  Qed.

  Lemma proves_provesN Δ ϕ :
    (Δ ⊢ᴮ ϕ) → ∃ n, Δ ⊢ᴮ{n} ϕ.
  Proof.
    induction 1.
    all: try destruct IHproves as [n IH].
    all: try (destruct IHproves1 as [n1 IH1];
              destruct IHproves2 as [n2 IH2]).
    all: try by eexists; econstructor; eauto.
  Qed.

  (** * Inversion lemmas *)
  Local Ltac bind_ctx :=
    match goal with
    | [ |- fill ?C ?Δ,, ?Δ' ⊢ᴮ{_} _ ] =>
      replace (fill C Δ,, Δ')%B
      with (fill (C ++ [CtxCommaL Δ']) Δ)%B
      by rewrite fill_app//
    | [ |- fill ?C ?Δ;, ?Δ' ⊢ᴮ{_} _ ] =>
      replace (fill C Δ;, Δ')%B
      with (fill (C ++ [CtxSemicL Δ']) Δ)%B
      by rewrite fill_app//
    end.

  Local Ltac commute_left_rule IH :=
    intros ->; bind_ctx;
    econstructor; eauto; rewrite fill_app; by eapply IH.

  Lemma wand_r_inv Δ ϕ ψ n :
    (Δ ⊢ᴮ{n} WAND ϕ ψ) →
    (Δ ,, frml ϕ ⊢ᴮ{n} ψ)%B.
  Proof.
    remember (WAND ϕ ψ) as A.
    intros H. revert ϕ ψ HeqA.
    induction H; intros A B; try by inversion 1.
    all: try by (commute_left_rule IHproves).
    - intros ->. by constructor; apply IHproves.
    - intros ->. eapply BI_Equiv.
      { rewrite -H. reflexivity. }
      by apply IHproves.
    - intros ?; simplify_eq/=. by apply BI_Higher.
    - commute_left_rule IHproves2.
    - commute_left_rule IHproves2.
  Qed.

  Lemma impl_r_inv Δ ϕ ψ n :
    (Δ ⊢ᴮ{n} IMPL ϕ ψ) →
    (Δ ;, frml ϕ ⊢ᴮ{n} ψ)%B.
  Proof.
    remember (IMPL ϕ ψ) as A.
    intros H. revert ϕ ψ HeqA.
    induction H; intros A B; try by inversion 1.
    all: try by (commute_left_rule IHproves).
    - intros ->. by constructor; apply IHproves.
    - intros ->. eapply BI_Equiv.
      { rewrite -H. reflexivity. }
      by apply IHproves.
    - commute_left_rule IHproves2.
    - intros ?; simplify_eq/=. by apply BI_Higher.
    - commute_left_rule IHproves2.
  Qed.

  Lemma sep_l_inv' Δ C ϕ ψ χ n :
    (Δ ⊢ᴮ{n} χ) →
    Δ = fill C (frml (SEP ϕ ψ)) →
    (fill C (frml ϕ,, frml ψ) ⊢ᴮ{n} χ).
  Proof.
    revert C Δ χ.
    induction n using lt_wf_ind. rename H into IHproves.
    intros C Δ χ PROOF Heq. symmetry in Heq. revert Heq.
    inversion PROOF; simplify_eq/= => Heq.
    (* induction H => C' Heq; symmetry in Heq. *)
    - (* raising the pf height *)
      apply BI_Higher.
      eapply IHproves; eauto.
    - (* axiom *)
      apply fill_is_frml in Heq. destruct_and!; simplify_eq/=.
      (* eapply BI_Sep_R; by econstructor. *)
    - (* equivalence of bunches *)
      simplify_eq/=.
      destruct (bunch_equiv_fill _ _ _ H) as [C2 [-> HC2]].
      eapply BI_Equiv.
      { apply HC2. }
      eapply IHproves; eauto.
    - (* weakening *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        * rewrite !fill_app/=.
          apply BI_Weaken.
          rewrite -fill_app.
          eapply IHproves; eauto.
          by apply bunch_decomp_correct, bunch_decomp_app.
        * rewrite !fill_app/=.
          by apply BI_Weaken.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Weaken.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* contraction *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2]; last first.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Contr.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
      + rename C0 into C'.
        destruct H1 as [C0 [HC0 ->]].
        apply bunch_decomp_correct in HC0.
        simplify_eq/=.
        assert (fill C' (fill C0 (frml ϕ,, frml ψ);, fill C0 (frml (SEP ϕ ψ))) ⊢ᴮ{ n0} χ) as IH1.
        { specialize (IHproves n0 (lt_n_Sn _)).
          set (C2 := (C0 ++ [CtxSemicL (fill C0 (frml (SEP ϕ ψ)))] ++ C')%B).
          specialize (IHproves C2 _ _ H).
          revert IHproves. rewrite /C2 !fill_app /=.
          eauto. }
        rewrite fill_app.
        apply BI_Contr.
        set (C2 := (C0 ++ [CtxSemicR (fill C0 (frml ϕ,, frml ψ))] ++ C')%B).
        replace (fill C' (fill C0 (frml ϕ,, frml ψ);, fill C0 (frml ϕ,, frml ψ)))%B
                   with (fill C2 (frml ϕ,, frml ψ))%B by rewrite fill_app//.
        eapply IHproves; eauto.
        rewrite /C2 fill_app//.
    - (* emp R *)
      exfalso.
      apply bunch_decomp_complete in Heq.
      inversion Heq.
    - (* emp L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Emp_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* sep R *)
      apply bunch_decomp_complete in Heq.
      inversion Heq; simplify_eq/=.
      + rewrite fill_app /=.
        eapply BI_Sep_R; eauto.
        eapply IHproves; eauto; first lia.
        by apply bunch_decomp_correct.
      + rewrite fill_app /=.
        eapply BI_Sep_R; eauto.
        eapply IHproves; eauto; first lia.
        by apply bunch_decomp_correct.
    - (* sep L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        by apply BI_Higher.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Sep_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* wand R *)
      apply BI_Wand_R.
      assert ((fill C (frml ϕ,, frml ψ),, frml ϕ0) =
                   fill (C ++ [CtxCommaL (frml ϕ0)]) (frml ϕ,, frml ψ))%B as ->.
      { rewrite fill_app//. }
      eapply IHproves; eauto. rewrite -Heq fill_app /= //.
    - (* wand L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        * rewrite !fill_app/=.
          eapply BI_Wand_L; eauto.
          eapply IHproves; eauto; first lia.
          by apply bunch_decomp_correct.
        * exfalso. inversion H5.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Wand_L; eauto.
        rewrite -HC0.
        eapply IHproves; eauto; first lia.
        apply bunch_decomp_correct. apply Hdec0.
    - (* bot L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_False_L.
    - (* top R *) apply BI_True_R.
    - (* top L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_True_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* conjR *)
      apply bunch_decomp_complete in Heq.
      inversion Heq; simplify_eq/=.
      + rewrite fill_app /=.
        eapply BI_Conj_R; eauto.
        eapply IHproves; eauto; first lia.
        by apply bunch_decomp_correct.
      + rewrite fill_app /=.
        eapply BI_Conj_R; eauto.
        eapply IHproves; eauto; first lia.
        by apply bunch_decomp_correct.
    - (* conjL *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Conj_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* impl R *)
      apply BI_Impl_R.
      assert ((fill C (frml ϕ,, frml ψ);, frml ϕ0) =
                   fill (C ++ [CtxSemicL (frml ϕ0)]) (frml ϕ,, frml ψ))%B as ->.
      { rewrite fill_app//. }
      eapply IHproves; eauto. rewrite -Heq fill_app /= //.
    -       apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        * rewrite !fill_app/=.
          eapply BI_Impl_L; eauto.
          eapply IHproves; eauto; first lia.
          by apply bunch_decomp_correct.
        * exfalso. inversion H5.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Impl_L; eauto.
        rewrite -HC0.
        eapply IHproves; eauto; first lia.
        apply bunch_decomp_correct. apply Hdec0.
  Qed.

  Lemma conj_l_inv' Δ C ϕ ψ χ n :
    (Δ ⊢ᴮ{n} χ) →
    Δ = fill C (frml (CONJ ϕ ψ)) →
    (fill C (frml ϕ;, frml ψ) ⊢ᴮ{n} χ).
  Proof.
    revert C Δ χ.
    induction n using lt_wf_ind. rename H into IHproves.
    intros C Δ χ PROOF Heq. symmetry in Heq. revert Heq.
    inversion PROOF; simplify_eq/= => Heq.
    (* induction H => C' Heq; symmetry in Heq. *)
    - (* raising the pf height *)
      apply BI_Higher.
      eapply IHproves; eauto.
    - (* axiom *)
      apply fill_is_frml in Heq. destruct_and!; simplify_eq/=.
      (* eapply BI_Sep_R; by econstructor. *)
    - (* equivalence of bunches *)
      simplify_eq/=.
      destruct (bunch_equiv_fill _ _ _ H) as [C2 [-> HC2]].
      eapply BI_Equiv.
      { apply HC2. }
      eapply IHproves; eauto.
    - (* weakening *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        * rewrite !fill_app/=.
          apply BI_Weaken.
          rewrite -fill_app.
          eapply IHproves; eauto.
          by apply bunch_decomp_correct, bunch_decomp_app.
        * rewrite !fill_app/=.
          by apply BI_Weaken.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Weaken.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* contraction *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2]; last first.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Contr.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
      + rename C0 into C'.
        destruct H1 as [C0 [HC0 ->]].
        apply bunch_decomp_correct in HC0.
        simplify_eq/=.
        assert (fill C' (fill C0 (frml ϕ;, frml ψ);, fill C0 (frml (CONJ ϕ ψ))) ⊢ᴮ{ n0} χ) as IH1.
        { specialize (IHproves n0 (lt_n_Sn _)).
          set (C2 := (C0 ++ [CtxSemicL (fill C0 (frml (CONJ ϕ ψ)))] ++ C')%B).
          specialize (IHproves C2 _ _ H).
          revert IHproves. rewrite /C2 !fill_app /=.
          eauto. }
        rewrite fill_app.
        apply BI_Contr.
        set (C2 := (C0 ++ [CtxSemicR (fill C0 (frml ϕ;, frml ψ))] ++ C')%B).
        replace (fill C' (fill C0 (frml ϕ;, frml ψ);, fill C0 (frml ϕ;, frml ψ)))%B
                   with (fill C2 (frml ϕ;, frml ψ))%B by rewrite fill_app//.
        eapply IHproves; eauto.
        rewrite /C2 fill_app//.
    - (* emp R *)
      exfalso.
      apply bunch_decomp_complete in Heq.
      inversion Heq.
    - (* emp L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Emp_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* sep R *)
      apply bunch_decomp_complete in Heq.
      inversion Heq; simplify_eq/=.
      + rewrite fill_app /=.
        eapply BI_Sep_R; eauto.
        eapply IHproves; eauto; first lia.
        by apply bunch_decomp_correct.
      + rewrite fill_app /=.
        eapply BI_Sep_R; eauto.
        eapply IHproves; eauto; first lia.
        by apply bunch_decomp_correct.
    - (* sep L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Sep_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* wand R *)
      apply BI_Wand_R.
      assert ((fill C (frml ϕ;, frml ψ),, frml ϕ0) =
                   fill (C ++ [CtxCommaL (frml ϕ0)]) (frml ϕ;, frml ψ))%B as ->.
      { rewrite fill_app//. }
      eapply IHproves; eauto. rewrite -Heq fill_app /= //.
    - (* wand L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        * rewrite !fill_app/=.
          eapply BI_Wand_L; eauto.
          eapply IHproves; eauto; first lia.
          by apply bunch_decomp_correct.
        * exfalso. inversion H5.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Wand_L; eauto.
        rewrite -HC0.
        eapply IHproves; eauto; first lia.
        apply bunch_decomp_correct. apply Hdec0.
    - (* bot L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_False_L.
    - (* top R *) apply BI_True_R.
    - (* top L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_True_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* conjR *)
      apply bunch_decomp_complete in Heq.
      inversion Heq; simplify_eq/=.
      + rewrite fill_app /=.
        eapply BI_Conj_R; eauto.
        eapply IHproves; eauto; first lia.
        by apply bunch_decomp_correct.
      + rewrite fill_app /=.
        eapply BI_Conj_R; eauto.
        eapply IHproves; eauto; first lia.
        by apply bunch_decomp_correct.
    - (* conjL *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        by apply BI_Higher.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Conj_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* impl R *)
      apply BI_Impl_R.
      assert ((fill C (frml ϕ;, frml ψ);, frml ϕ0) =
                   fill (C ++ [CtxSemicL (frml ϕ0)]) (frml ϕ;, frml ψ))%B as ->.
      { rewrite fill_app//. }
      eapply IHproves; eauto. rewrite -Heq fill_app /= //.
    -       apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        * rewrite !fill_app/=.
          eapply BI_Impl_L; eauto.
          eapply IHproves; eauto; first lia.
          by apply bunch_decomp_correct.
        * exfalso. inversion H5.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Impl_L; eauto.
        rewrite -HC0.
        eapply IHproves; eauto; first lia.
        apply bunch_decomp_correct. apply Hdec0.
  Qed.

  Lemma top_l_inv' Δ C ϕ ψ χ n :
    (Δ ⊢ᴮ{n} χ) →
    Δ = fill C (frml TOP) →
    (fill C top ⊢ᴮ{n} χ).
  Proof.
    revert C Δ χ.
    induction n using lt_wf_ind. rename H into IHproves.
    intros C Δ χ PROOF Heq. symmetry in Heq. revert Heq.
    inversion PROOF; simplify_eq/= => Heq.
    (* induction H => C' Heq; symmetry in Heq. *)
    - (* raising the pf height *)
      apply BI_Higher.
      eapply IHproves; eauto.
    - (* axiom *)
      apply fill_is_frml in Heq. destruct_and!; simplify_eq/=.
    - (* equivalence of bunches *)
      simplify_eq/=.
      destruct (bunch_equiv_fill _ _ _ H) as [C2 [-> HC2]].
      eapply BI_Equiv.
      { apply HC2. }
      eapply IHproves; eauto.
    - (* weakening *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        * rewrite !fill_app/=.
          apply BI_Weaken.
          rewrite -fill_app.
          eapply IHproves; eauto.
          by apply bunch_decomp_correct, bunch_decomp_app.
        * rewrite !fill_app/=.
          by apply BI_Weaken.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Weaken.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* contraction *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2]; last first.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Contr.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
      + rename C0 into C'.
        destruct H1 as [C0 [HC0 ->]].
        apply bunch_decomp_correct in HC0.
        simplify_eq/=.
        assert (fill C' (fill C0 top;, fill C0 (frml TOP)) ⊢ᴮ{ n0} χ) as IH1.
        { specialize (IHproves n0 (lt_n_Sn _)).
          set (C2 := (C0 ++ [CtxSemicL (fill C0 (frml TOP))] ++ C')%B).
          specialize (IHproves C2 _ _ H).
          revert IHproves. rewrite /C2 !fill_app /=.
          eauto. }
        rewrite fill_app.
        apply BI_Contr.
        set (C2 := (C0 ++ [CtxSemicR (fill C0 top)] ++ C')%B).
        replace (fill C' (fill C0 top;, fill C0 top))%B
                   with (fill C2 top)%B by rewrite fill_app//.
        eapply IHproves; eauto.
        rewrite /C2 fill_app//.
    - (* emp R *)
      exfalso.
      apply bunch_decomp_complete in Heq.
      inversion Heq.
    - (* emp L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Emp_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* sep R *)
      apply bunch_decomp_complete in Heq.
      inversion Heq; simplify_eq/=.
      + rewrite fill_app /=.
        eapply BI_Sep_R; eauto.
        eapply IHproves; eauto; first lia.
        by apply bunch_decomp_correct.
      + rewrite fill_app /=.
        eapply BI_Sep_R; eauto.
        eapply IHproves; eauto; first lia.
        by apply bunch_decomp_correct.
    - (* sep L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Sep_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* wand R *)
      apply BI_Wand_R.
      assert ((fill C top,, frml ϕ0) =
                   fill (C ++ [CtxCommaL (frml ϕ0)]) top)%B as ->.
      { rewrite fill_app//. }
      eapply IHproves; eauto. rewrite -Heq fill_app /= //.
    - (* wand L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        * rewrite !fill_app/=.
          eapply BI_Wand_L; eauto.
          eapply IHproves; eauto; first lia.
          by apply bunch_decomp_correct.
        * exfalso. inversion H5.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Wand_L; eauto.
        rewrite -HC0.
        eapply IHproves; eauto; first lia.
        apply bunch_decomp_correct. apply Hdec0.
    - (* bot L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_False_L.
    - (* top R *) apply BI_True_R.
    - (* top L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        by eapply BI_Higher.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_True_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* conjR *)
      apply bunch_decomp_complete in Heq.
      inversion Heq; simplify_eq/=.
      + rewrite fill_app /=.
        eapply BI_Conj_R; eauto.
        eapply IHproves; eauto; first lia.
        by apply bunch_decomp_correct.
      + rewrite fill_app /=.
        eapply BI_Conj_R; eauto.
        eapply IHproves; eauto; first lia.
        by apply bunch_decomp_correct.
    - (* conjL *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Conj_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* impl R *)
      apply BI_Impl_R.
      assert ((fill C top;, frml ϕ0) =
                   fill (C ++ [CtxSemicL (frml ϕ0)]) top)%B as ->.
      { rewrite fill_app//. }
      eapply IHproves; eauto. rewrite -Heq fill_app /= //.
    -       apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        * rewrite !fill_app/=.
          eapply BI_Impl_L; eauto.
          eapply IHproves; eauto; first lia.
          by apply bunch_decomp_correct.
        * exfalso. inversion H5.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Impl_L; eauto.
        rewrite -HC0.
        eapply IHproves; eauto; first lia.
        apply bunch_decomp_correct. apply Hdec0.
  Qed.

  Lemma emp_l_inv' Δ C ϕ ψ χ n :
    (Δ ⊢ᴮ{n} χ) →
    Δ = fill C (frml EMP) →
    (fill C empty ⊢ᴮ{n} χ).
  Proof.
    revert C Δ χ.
    induction n using lt_wf_ind. rename H into IHproves.
    intros C Δ χ PROOF Heq. symmetry in Heq. revert Heq.
    inversion PROOF; simplify_eq/= => Heq.
    (* induction H => C' Heq; symmetry in Heq. *)
    - (* raising the pf height *)
      apply BI_Higher.
      eapply IHproves; eauto.
    - (* axiom *)
      apply fill_is_frml in Heq. destruct_and!; simplify_eq/=.
    - (* equivalence of bunches *)
      simplify_eq/=.
      destruct (bunch_equiv_fill _ _ _ H) as [C2 [-> HC2]].
      eapply BI_Equiv.
      { apply HC2. }
      eapply IHproves; eauto.
    - (* weakening *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        * rewrite !fill_app/=.
          apply BI_Weaken.
          rewrite -fill_app.
          eapply IHproves; eauto.
          by apply bunch_decomp_correct, bunch_decomp_app.
        * rewrite !fill_app/=.
          by apply BI_Weaken.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Weaken.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* contraction *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2]; last first.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Contr.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
      + rename C0 into C'.
        destruct H1 as [C0 [HC0 ->]].
        apply bunch_decomp_correct in HC0.
        simplify_eq/=.
        assert (fill C' (fill C0 empty;, fill C0 (frml EMP)) ⊢ᴮ{ n0} χ) as IH1.
        { specialize (IHproves n0 (lt_n_Sn _)).
          set (C2 := (C0 ++ [CtxSemicL (fill C0 (frml EMP))] ++ C')%B).
          specialize (IHproves C2 _ _ H).
          revert IHproves. rewrite /C2 !fill_app /=.
          eauto. }
        rewrite fill_app.
        apply BI_Contr.
        set (C2 := (C0 ++ [CtxSemicR (fill C0 empty)] ++ C')%B).
        replace (fill C' (fill C0 empty;, fill C0 empty))%B
                   with (fill C2 empty)%B by rewrite fill_app//.
        eapply IHproves; eauto.
        rewrite /C2 fill_app//.
    - (* emp R *)
      exfalso.
      apply bunch_decomp_complete in Heq.
      inversion Heq.
    - (* emp L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        by eapply BI_Higher.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Emp_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* sep R *)
      apply bunch_decomp_complete in Heq.
      inversion Heq; simplify_eq/=.
      + rewrite fill_app /=.
        eapply BI_Sep_R; eauto.
        eapply IHproves; eauto; first lia.
        by apply bunch_decomp_correct.
      + rewrite fill_app /=.
        eapply BI_Sep_R; eauto.
        eapply IHproves; eauto; first lia.
        by apply bunch_decomp_correct.
    - (* sep L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Sep_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* wand R *)
      apply BI_Wand_R.
      assert ((fill C empty,, frml ϕ0) =
                   fill (C ++ [CtxCommaL (frml ϕ0)]) empty)%B as ->.
      { rewrite fill_app//. }
      eapply IHproves; eauto. rewrite -Heq fill_app /= //.
    - (* wand L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        * rewrite !fill_app/=.
          eapply BI_Wand_L; eauto.
          eapply IHproves; eauto; first lia.
          by apply bunch_decomp_correct.
        * exfalso. inversion H5.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Wand_L; eauto.
        rewrite -HC0.
        eapply IHproves; eauto; first lia.
        apply bunch_decomp_correct. apply Hdec0.
    - (* bot L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_False_L.
    - (* true R *) apply BI_True_R.
    - (* true L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_True_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* conjR *)
      apply bunch_decomp_complete in Heq.
      inversion Heq; simplify_eq/=.
      + rewrite fill_app /=.
        eapply BI_Conj_R; eauto.
        eapply IHproves; eauto; first lia.
        by apply bunch_decomp_correct.
      + rewrite fill_app /=.
        eapply BI_Conj_R; eauto.
        eapply IHproves; eauto; first lia.
        by apply bunch_decomp_correct.
    - (* conjL *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Conj_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* impl R *)
      apply BI_Impl_R.
      assert ((fill C empty;, frml ϕ0) =
                   fill (C ++ [CtxSemicL (frml ϕ0)]) empty)%B as ->.
      { rewrite fill_app//. }
      eapply IHproves; eauto. rewrite -Heq fill_app /= //.
    -       apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        * rewrite !fill_app/=.
          eapply BI_Impl_L; eauto.
          eapply IHproves; eauto; first lia.
          by apply bunch_decomp_correct.
        * exfalso. inversion H5.
      + rename C0 into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Impl_L; eauto.
        rewrite -HC0.
        eapply IHproves; eauto; first lia.
        apply bunch_decomp_correct. apply Hdec0.
  Qed.

End bunchHeight.

(** Derivable rules / inversion lemmas *)
Lemma impl_r_inv Δ ϕ ψ :
  (Δ ⊢ᴮ IMPL ϕ ψ) →
  (Δ ;, frml ϕ ⊢ᴮ ψ)%B.
Proof.
  intros [n H]%bunchHeight.proves_provesN.
  eapply bunchHeight.provesN_proves.
  by apply bunchHeight.impl_r_inv.
Qed.
Lemma wand_r_inv Δ ϕ ψ :
  (Δ ⊢ᴮ WAND ϕ ψ) →
  (Δ ,, frml ϕ ⊢ᴮ ψ)%B.
Proof.
  intros [n H]%bunchHeight.proves_provesN.
  eapply bunchHeight.provesN_proves.
  by apply bunchHeight.wand_r_inv.
Qed.
Lemma sep_l_inv C ϕ ψ χ :
  (fill C (frml (SEP ϕ ψ)) ⊢ᴮ χ) →
  (fill C (frml ϕ,, frml ψ) ⊢ᴮ χ).
Proof.
  intros [n H]%bunchHeight.proves_provesN.
  eapply bunchHeight.provesN_proves.
  eapply bunchHeight.sep_l_inv'; eauto.
Qed.
Lemma conj_l_inv C ϕ ψ χ :
  (fill C (frml (CONJ ϕ ψ)) ⊢ᴮ χ) →
  (fill C (frml ϕ;, frml ψ) ⊢ᴮ χ).
Proof.
  intros [n H]%bunchHeight.proves_provesN.
  eapply bunchHeight.provesN_proves.
  eapply bunchHeight.conj_l_inv'; eauto.
Qed.
Lemma collapse_l_inv C Δ ϕ :
  (fill C (frml (collapse Δ)) ⊢ᴮ ϕ) →
  (fill C Δ ⊢ᴮ ϕ).
Proof.
  revert C. induction Δ; simpl; first done.
  - intros C [n H]%bunchHeight.proves_provesN.
    eapply bunchHeight.provesN_proves.
    eapply bunchHeight.top_l_inv'; eauto.
  - intros C [n H]%bunchHeight.proves_provesN.
    eapply bunchHeight.provesN_proves.
    eapply bunchHeight.emp_l_inv'; eauto.
  - intros C H1.
    replace (fill C (Δ1,, Δ2))%B
      with (fill (CtxCommaR Δ1::C) Δ2) by reflexivity.
    apply IHΔ2. simpl.
    replace (fill C (Δ1,, frml (collapse Δ2)))%B
      with (fill (CtxCommaL (frml (collapse Δ2))::C) Δ1) by reflexivity.
    apply IHΔ1. simpl.
    by apply sep_l_inv.
  - intros C H1.
    replace (fill C (Δ1;, Δ2))%B
      with (fill (CtxSemicR Δ1::C) Δ2) by reflexivity.
    apply IHΔ2. simpl.
    replace (fill C (Δ1;, frml (collapse Δ2)))%B
      with (fill (CtxSemicL (frml (collapse Δ2))::C) Δ1) by reflexivity.
    apply IHΔ1. simpl.
    by apply conj_l_inv.
Qed.
