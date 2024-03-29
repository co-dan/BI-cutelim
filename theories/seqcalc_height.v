(* Sequent calculus with upper bounds on proof size.
   Useful for doing induction on.

   The main purpose this file is to provide the inversion lemmas (see the bottom part of the file).
 *)
From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From bunched.algebra Require Import bi.
From bunched Require Import seqcalc bunch_decomp prelude.lists.

Reserved Notation "P ⊢ᴮ{ n } Q" (at level 99, n, Q at level 200, right associativity).
Reserved Notation "Δ =?{ n } Δ'" (at level 99, n at level 200).

Module SeqcalcHeight(R : ANALYTIC_STRUCT_EXT).
  Import R.
  Module S := Seqcalc(R).
  Import S.

  Implicit Type Δ : bunch.
  Implicit Type ψ ϕ : formula.

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
  | BI_Simple_Ext Π (Δs : nat → bunch) n
    (Ts : list bterm) (T : bterm) ϕ :
    (Ts, T) ∈ rules →
    (∀ Ti, Ti ∈ Ts → fill Π (bterm_ctx_act Ti Δs) ⊢ᴮ{n} ϕ) →
    fill Π (bterm_ctx_act T Δs) ⊢ᴮ{S n} ϕ
  (* multiplicatives *)
  | BI_Emp_R :
      ∅ₘ ⊢ᴮ{0} EMP
  | BI_Emp_L C ϕ n :
      (fill C ∅ₘ ⊢ᴮ{n} ϕ) →
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
      (fill C ∅ₐ ⊢ᴮ{n} ϕ) →
      fill C (frml TOP) ⊢ᴮ{S n} ϕ
  | BI_Conj_R Δ Δ' ϕ ψ n m :
      (Δ ⊢ᴮ{n} ϕ) →
      (Δ' ⊢ᴮ{m} ψ) →
      Δ ;, Δ' ⊢ᴮ{S (n `max` m)} CONJ ϕ ψ
  | BI_Conj_L C ϕ ψ χ n :
      (fill C (frml ϕ ;, frml ψ) ⊢ᴮ{n} χ) →
      fill C (frml (CONJ ϕ ψ)) ⊢ᴮ{S n} χ
  | BI_Disj_R1 Δ ϕ ψ n :
      (Δ ⊢ᴮ{n} ϕ) →
      Δ ⊢ᴮ{S n} DISJ ϕ ψ
  | BI_Disj_R2 Δ ϕ ψ n :
      (Δ ⊢ᴮ{n} ψ) →
      Δ ⊢ᴮ{S n} DISJ ϕ ψ
  | BI_Disj_L Π ϕ ψ χ n m :
      (fill Π (frml ϕ) ⊢ᴮ{n} χ) →
      (fill Π (frml ψ) ⊢ᴮ{m} χ) →
      fill Π (frml (DISJ ϕ ψ)) ⊢ᴮ{S (n `max` m)} χ
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
    induction 1; try by econstructor; eauto.
    (* XXX: somehow, [try] is really needed here ^ *)
  Qed.

  Lemma proves_le n m Δ ϕ :
    n ≤ m → (Δ ⊢ᴮ{n} ϕ) → Δ ⊢ᴮ{m} ϕ.
  Proof.
    induction 1; auto.
    intros H1. eapply BI_Higher. eauto.
  Qed.

  Lemma proves_provesN Δ ϕ :
    (Δ ⊢ᴮ ϕ) → ∃ n, Δ ⊢ᴮ{n} ϕ.
  Proof.
    induction 1.
    all: try destruct IHproves as [n IH].
    all: try (destruct IHproves1 as [n1 IH1];
              destruct IHproves2 as [n2 IH2]).
    all: try by eexists; econstructor; eauto.
    (* The worst case: simple structural rules *)
    apply (Forall_forall (λ Ti, ∃ n : nat, fill Π (bterm_ctx_act Ti Δs) ⊢ᴮ{ n} ϕ)) in H1.
    apply Forall_exists_Forall2 in H1.
    destruct H1 as (ns & Hns).
    exists (S (max_list ns)).
    eapply BI_Simple_Ext; eauto.
    intros Ti HTi.
    destruct (elem_of_list_lookup_1 _ _ HTi) as [i Hi].
    destruct (ns !! i) as [n|] eqn:Hn; last first.
    { eapply Forall2_lookup_r in Hns; eauto.
      naive_solver. }
    eapply (proves_le n). {
      eapply max_list_elem_of_le.
      by eapply elem_of_list_lookup_2.
    }
    eapply Forall2_lookup_lr in Hns; eauto.
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

  Lemma wand_r_inv' Δ ϕ ψ n :
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
    - intros ->. bind_ctx.
      eapply BI_Simple_Ext; eauto.
      intros Ti HTi. rewrite fill_app. simpl.
      eapply H1; eauto.
    - intros ?; simplify_eq/=. by apply BI_Higher.
    - commute_left_rule IHproves2.
    - intros ?; simplify_eq/=.
      bind_ctx. eapply BI_Disj_L.
      + rewrite fill_app/=. by eapply IHproves1.
      + rewrite fill_app/=. by eapply IHproves2.
    - commute_left_rule IHproves2.
  Qed.

  Lemma impl_r_inv' Δ ϕ ψ n :
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
    - intros ->. bind_ctx.
      eapply BI_Simple_Ext; eauto.
      intros Ti HTi. rewrite fill_app. simpl.
      eapply H1; eauto.
    - commute_left_rule IHproves2.
    - intros ?; simplify_eq/=.
      bind_ctx. eapply BI_Disj_L.
      + rewrite fill_app/=. by eapply IHproves1.
      + rewrite fill_app/=. by eapply IHproves2.
    - intros ?; simplify_eq/=. by apply BI_Higher.
    - commute_left_rule IHproves2.
  Qed.

  Lemma collapse_l_inv' Δ Π Δ' ϕ χ n :
    collapse_gr Δ' ϕ →
    (Δ ⊢ᴮ{n} χ) →
    Δ = fill Π (frml ϕ) →
    (fill Π Δ' ⊢ᴮ{n} χ).
  Proof.
    revert Π Δ Δ' ϕ χ.
    induction n as [n IHproves] using lt_wf_ind.
    intros Π Δ Δ' ϕ χ Hcoll PROOF Heq. symmetry in Heq. revert Heq.
    inversion PROOF; simplify_eq/= => Heq.
    (* induction H => C' Heq; symmetry in Heq. *)
    - (* raising the pf height *)
      apply BI_Higher.
      eapply IHproves; eauto.
    - (* axiom *)
      apply fill_is_frml in Heq. destruct_and!; simplify_eq/=.
      inversion Hcoll. by econstructor.
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
      + rename C into C'.
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
      + rename C into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Contr.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
      + rename C into C'.
        destruct H1 as [C0 [HC0 ->]].
        apply bunch_decomp_correct in HC0.
        simplify_eq/=.
        assert (fill C' (fill C0 Δ';, fill C0 (frml ϕ)) ⊢ᴮ{ n0} χ) as IH1.
        { specialize (IHproves n0 (lt_n_Sn _)).
          set (C2 := (C0 ++ [CtxSemicL (fill C0 (frml ϕ))] ++ C')%B).
          specialize (IHproves C2 _ _ _ _ Hcoll H).
          revert IHproves. rewrite /C2 !fill_app /=.
          eauto. }
        rewrite fill_app.
        apply BI_Contr.
        set (C2 := (C0 ++ [CtxSemicR (fill C0 Δ')] ++ C')%B).
        replace (fill C' (fill C0 Δ';, fill C0 Δ'))%B
                   with (fill C2 Δ')%B by rewrite fill_app//.
        eapply IHproves; eauto.
        rewrite /C2 fill_app//.
    - (* ext *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2]; last first.
      + destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        eapply BI_Simple_Ext; eauto.
        intros Ti Hi.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
      + destruct H1 as [C0 [HC0 ->]].
        apply bunch_decomp_correct in HC0.
        simplify_eq/=.
        apply bterm_ctx_act_decomp in HC0; last first.
        { by eapply (rules_good (Ts,T)). }
        destruct HC0 as (j & Π₀ & Hjfv & Hj & HC0).
        rewrite fill_app -HC0.
        eapply BI_Simple_Ext; eauto.
        revert Hj Hjfv IHproves H0 Hcoll.
        clear.
        intros Hj Hjfv IHproves Hpfs Hcoll.
        intros Ti HTi. specialize (Hpfs Ti HTi).
        revert Π0 Hpfs. clear HTi.
        induction Ti=>Π0 Hpfs.
        { simpl.
          destruct (decide (j = x)) as [->|?].
          - rewrite functions.fn_lookup_insert.
            rewrite -fill_app. simpl in Hpfs.
            eapply IHproves; eauto.
            by rewrite fill_app -Hj.
          - rewrite functions.fn_lookup_insert_ne; auto. }
        { simpl.
          assert (fill ([CtxL sp (bterm_ctx_act Ti2 Δs)]++Π0) (bterm_ctx_act Ti1 (<[j:=fill Π₀ Δ']> Δs)) ⊢ᴮ{ n0} χ) as HH1.
          { eapply IHTi1. rewrite fill_app /=. eauto. }
          rewrite fill_app in HH1.
          simpl in HH1.
          replace
            (fill Π0 (bbin sp
                       (bterm_ctx_act Ti1
             (<[j:=fill Π₀ Δ']> Δs)) (bterm_ctx_act Ti2 (<[j:=fill Π₀ Δ']> Δs))))%B
            with
          (fill ([CtxR sp (bterm_ctx_act Ti1 (<[j:=fill Π₀ Δ']> Δs))]++Π0)
                (bterm_ctx_act Ti2 (<[j:=fill Π₀ Δ']> Δs)))%B
            by rewrite fill_app//.
          eapply IHTi2.
          rewrite fill_app/=//. }
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
        inversion Hcoll; simplify_eq/=.
        * by apply BI_Emp_L.
        * by apply BI_Higher.
      + rename C into C'.
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
        inversion Hcoll; simplify_eq/=; eauto.
        assert (fill C (Δ1,, frml ψ) ⊢ᴮ{ n0} χ) as H1.
        { replace (fill C (Δ1,, frml ψ))%B
            with (fill ([CtxCommaL (frml ψ)]++C) Δ1)
            by rewrite fill_app//.
          eapply IHproves; eauto. }
        replace (fill C (Δ1,, Δ2))%B
          with (fill ([CtxCommaR Δ1]++C) Δ2)
          by rewrite fill_app//.
        apply BI_Higher.
        eapply IHproves; eauto.
      + rename C into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Sep_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* wand R *)
      apply BI_Wand_R.
      replace (fill Π Δ',, frml ϕ0)%B
        with (fill (Π ++ [CtxCommaL (frml ϕ0)]) Δ')%B
        by rewrite fill_app//.
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
        * inversion H6; subst.
          inversion Hcoll; subst.
          simpl.
          eapply BI_Wand_L; eauto.
      + rename C into C'.
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
        inversion Hcoll; eauto.
      + rename C into C'.
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
        inversion Hcoll; subst; eauto.
        by apply BI_Higher.
      + rename C into C'.
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
        inversion Hcoll; simplify_eq/=; eauto.
        assert (fill C (Δ1;, frml ψ) ⊢ᴮ{ n0} χ) as H1.
        { replace (fill C (Δ1;, frml ψ))%B
            with (fill ([CtxSemicL (frml ψ)]++C) Δ1)
            by rewrite fill_app//.
          eapply IHproves; eauto. }
        replace (fill C (Δ1;, Δ2))%B
          with (fill ([CtxSemicR Δ1]++C) Δ2)
          by rewrite fill_app//.
        apply BI_Higher.
        eapply IHproves; eauto.
      + rename C into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Conj_L.
        rewrite -HC0.
        eapply IHproves; eauto.
        apply bunch_decomp_correct. apply Hdec0.
    - (* disj R 1 *)
      eapply BI_Disj_R1.
      eapply IHproves; eauto.
    - (* disj R 2 *)
      eapply BI_Disj_R2.
      eapply IHproves; eauto.
    - (* disj L *)
      apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        inversion Hcoll; simplify_eq/=; eauto.
      + destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Disj_L.
        * rewrite -HC0.
          eapply IHproves; eauto; first lia.
          apply bunch_decomp_correct. apply Hdec0.
        * rewrite -HC0.
          eapply IHproves; eauto; first lia.
          apply bunch_decomp_correct. apply Hdec0.
    - (* impl R *)
      apply BI_Impl_R.
      replace (fill Π Δ';, frml ϕ0)%B
        with (fill (Π ++ [CtxSemicL (frml ϕ0)]) Δ')%B
        by rewrite fill_app//.
      eapply IHproves; eauto. rewrite -Heq fill_app /= //.
    - apply bunch_decomp_complete in Heq.
      apply bunch_decomp_ctx in Heq.
      destruct Heq as [H1 | H2].
      + destruct H1 as [C1 [HC0 HC]].
        inversion HC0; simplify_eq/=.
        * rewrite !fill_app/=.
          eapply BI_Impl_L; eauto.
          eapply IHproves; eauto; first lia.
          by apply bunch_decomp_correct.
        * inversion H6; subst.
          inversion Hcoll; simplify_eq/=; eauto.
      + rename C into C'.
        destruct H2 as (C0 & C1 & HC0 & HC1 & Hdec0).
        rewrite -HC1.
        apply BI_Impl_L; eauto.
        rewrite -HC0.
        eapply IHproves; eauto; first lia.
        apply bunch_decomp_correct. apply Hdec0.
  Qed.

  (** Derivable rules / inversion lemmas *)
  Lemma impl_r_inv Δ ϕ ψ :
    (Δ ⊢ᴮ IMPL ϕ ψ) →
    (Δ ;, frml ϕ ⊢ᴮ ψ)%B.
  Proof.
    intros [n H]%proves_provesN.
    eapply provesN_proves.
    by apply impl_r_inv'.
  Qed.
  Lemma wand_r_inv Δ ϕ ψ :
    (Δ ⊢ᴮ WAND ϕ ψ) →
    (Δ ,, frml ϕ ⊢ᴮ ψ)%B.
  Proof.
    intros [n H]%proves_provesN.
    eapply provesN_proves.
    by apply wand_r_inv'.
  Qed.
  Lemma sep_l_inv C ϕ ψ χ :
    (fill C (frml (SEP ϕ ψ)) ⊢ᴮ χ) →
    (fill C (frml ϕ,, frml ψ) ⊢ᴮ χ).
  Proof.
    intros [n H]%proves_provesN.
    eapply provesN_proves.
    eapply collapse_l_inv'; eauto.
    by repeat constructor.
  Qed.
  Lemma conj_l_inv C ϕ ψ χ :
    (fill C (frml (CONJ ϕ ψ)) ⊢ᴮ χ) →
    (fill C (frml ϕ;, frml ψ) ⊢ᴮ χ).
  Proof.
    intros [n H]%proves_provesN.
    eapply provesN_proves.
    eapply collapse_l_inv'; eauto.
    by repeat constructor.
  Qed.
  Lemma BI_Collapse_L_inv C Δ ϕ :
    (fill C (frml (collapse Δ)) ⊢ᴮ ϕ) →
    (fill C Δ ⊢ᴮ ϕ).
  Proof.
    intros [n H]%proves_provesN.
    eapply provesN_proves.
    eapply collapse_l_inv'; eauto.
    apply collapse_gr_sound.
  Qed.
End SeqcalcHeight.
