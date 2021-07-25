(** Inductive representation for decomposition of bunches, and associated properties *)
From Coq Require Import ssreflect.
From stdpp Require Import prelude gmap functions.
From Equations Require Import Equations.
From bunched Require Export syntax terms.

(** * Alternative representation of decomposition of bunches *)
(** We have an inductive type that characterizes when a bunch can be
  decomposed into a context and a sub-bunch. This essentially gives an
  us an inductive reasoning principle for equations [fill Π Δ = Δ']. *)
Inductive bunch_decomp :
  bunch → bunch_ctx → bunch → Prop :=
| decomp_id Δ : bunch_decomp Δ [] Δ
| decomp_comma_1 Δ1 Δ2 Π Δ :
    bunch_decomp Δ1 Π Δ →
    bunch_decomp (Δ1,,Δ2)%B (Π ++ [CtxCommaL Δ2]) Δ
| decomp_comma_2 Δ1 Δ2 Π Δ :
    bunch_decomp Δ2 Π Δ →
    bunch_decomp (Δ1,,Δ2)%B (Π ++ [CtxCommaR Δ1]) Δ
| decomp_semic_1 Δ1 Δ2 Π Δ :
    bunch_decomp Δ1 Π Δ →
    bunch_decomp (Δ1;,Δ2)%B (Π ++ [CtxSemicL Δ2]) Δ
| decomp_semic_2 Δ1 Δ2 Π Δ :
    bunch_decomp Δ2 Π Δ →
    bunch_decomp (Δ1;,Δ2)%B (Π ++ [CtxSemicR Δ1]) Δ.

(** [bunch_decomp Δ' Π Δ] completely characterizes [fill Π Δ = Δ'] *)
Lemma bunch_decomp_correct Δ Π Δ' :
  bunch_decomp Δ Π Δ' → Δ = fill Π Δ'.
Proof. induction 1; rewrite ?fill_app /= //; try by f_equiv. Qed.

Lemma bunch_decomp_complete' Π Δ' :
  bunch_decomp (fill Π Δ') Π Δ'.
Proof.
  revert Δ'. remember (reverse Π) as Πr.
  revert Π HeqΠr.
  induction Πr as [|HΠ Πr]=>Π HeqΠr.
  { assert (Π = []) as ->.
    {  by eapply (inj reverse). }
    simpl. intros. econstructor. }
  intros Δ'.
  assert (Π = reverse Πr ++ [HΠ]) as ->.
  { by rewrite -reverse_cons HeqΠr reverse_involutive. }
  rewrite fill_app /=.
  revert Δ'.
  induction HΠ=>Δ' /=; econstructor; eapply IHΠr; by rewrite reverse_involutive.
Qed.

Lemma bunch_decomp_complete Δ Π Δ' :
  (fill Π Δ' = Δ) →
  bunch_decomp Δ Π Δ'.
Proof. intros <-. apply bunch_decomp_complete'. Qed.

Lemma fill_is_frml Π Δ ϕ :
  fill Π Δ = frml ϕ →
  Π = [] ∧ Δ = frml ϕ.
Proof.
  revert Δ. induction Π as [| F C IH]=>Δ; first by eauto.
  destruct F ; simpl ; intros H1 ;
    destruct (IH _ H1) as [HC HΔ] ; by simplify_eq/=.
Qed.

Lemma bunch_decomp_app C C0 Δ Δ0 :
  bunch_decomp Δ C0 Δ0 →
  bunch_decomp (fill C Δ) (C0 ++ C) Δ0.
Proof.
  revert Δ Δ0 C0.
  induction C as [|F C]=>Δ Δ0 C0.
  { simpl. by rewrite app_nil_r. }
  intros HD.
  replace (C0 ++ F :: C) with ((C0 ++ [F]) ++ C); last first.
  { by rewrite -assoc. }
  apply IHC. destruct F; simpl; by econstructor.
Qed.

Lemma bunch_decomp_ctx C C' Δ ϕ :
  bunch_decomp (fill C Δ) C' (frml ϕ) →
  ((∃ C0, bunch_decomp Δ C0 (frml ϕ) ∧ C' = C0 ++ C) ∨
   (∃ (C0 C1 : bunch → bunch_ctx),
       (∀ Δ Δ', fill (C0 Δ) Δ' = fill (C1 Δ') Δ) ∧
       (∀ Δ', fill (C1 Δ') Δ = fill C' Δ') ∧
       (∀ A, bunch_decomp (fill C A) (C0 A) (frml ϕ)))).
Proof.
  revert Δ C'.
  induction C as [|F C]=>Δ C'; simpl.
  { remember (frml ϕ) as Γ1. intros Hdec.
    left. eexists. rewrite right_id. split; done. }
  simpl. intros Hdec.
  destruct (IHC _ _ Hdec) as [IH|IH].
  - destruct IH as [C0 [HC0 HC]].
    destruct F; simpl in *.
    + inversion HC0; simplify_eq/=.
      * left. eexists; split; eauto.
        rewrite -assoc //.
      * right.
        exists (λ A, (Π ++ [CtxCommaR A]) ++ C).
        exists (λ A, ([CtxCommaL (fill Π A)] ++ C)).
        repeat split.
        { intros A B. by rewrite /= -!assoc /= !fill_app. }
        { intros A. by rewrite /= -!assoc /= !fill_app. }
        { intros A. apply bunch_decomp_app. by econstructor. }
    + inversion HC0; simplify_eq/=.
      * right.
        exists (λ A, (Π ++ [CtxCommaL A]) ++ C).
        exists (λ A, ([CtxCommaR (fill Π A)] ++ C)).
        repeat split.
        { intros A B. by rewrite /= -!assoc /= !fill_app. }
        { intros A. by rewrite /= -!assoc /= !fill_app. }
        { intros A. apply bunch_decomp_app. by econstructor. }
      * left. eexists; split; eauto.
        rewrite -assoc //.
    + inversion HC0; simplify_eq/=.
      * left. eexists; split; eauto.
        rewrite -assoc //.
      * right.
        exists (λ A, (Π ++ [CtxSemicR A]) ++ C).
        exists (λ A, ([CtxSemicL (fill Π A)] ++ C)).
        repeat split.
        { intros A B. by rewrite /= -!assoc /= !fill_app. }
        { intros A. by rewrite /= -!assoc /= !fill_app. }
        { intros A. apply bunch_decomp_app. by econstructor. }
    + inversion HC0; simplify_eq/=.
      * right.
        exists (λ A, (Π ++ [CtxSemicL A]) ++ C).
        exists (λ A, ([CtxSemicR (fill Π A)] ++ C)).
        repeat split.
        { intros A B. by rewrite /= -!assoc /= !fill_app. }
        { intros A. by rewrite /= -!assoc /= !fill_app. }
        { intros A. apply bunch_decomp_app. by econstructor. }
      * left. eexists; split; eauto.
        rewrite -assoc //.
  - right.
    destruct IH as (C0 & C1 & HC0 & HC1 & HC).
    exists (λ A, C0 (fill_item F A)), (λ A, F::C1 A). repeat split.
    { intros A B. simpl. rewrite -HC0 //. }
    { intros B. rewrite -HC1 //. }
    intros A. apply HC.
Qed.


(* facts about terms *)
Lemma bterm_ctx_act_decomp `{!EqDecision V, !Countable V} (T : bterm V)
  (Δs : V → bunch) ϕ Π :
  linear_bterm T →
  bterm_ctx_act T Δs = fill Π (frml ϕ) →
  ∃ (j : V) Π₀ , j ∈ term_fv T ∧ Δs j = fill Π₀ (frml ϕ) ∧
   (∀ Δ, bterm_ctx_act T (<[j:=(fill Π₀ Δ)]>Δs) = fill Π Δ).
Proof.
  revert Π. induction T=>Π Hlin.
  - simpl.
    intros Hx. exists x, Π. repeat split; auto.
    { simp term_fv. set_solver. }
    intros Γ. by rewrite fn_lookup_insert.
  - simpl. simp linear_bterm in Hlin.
    destruct Hlin as (Ht12 & Hlin1 & Hlin2).
    intros Ht. symmetry in Ht.
    apply bunch_decomp_complete in Ht.
    inversion Ht; simplify_eq/=.
    + apply bunch_decomp_correct in H3.
      specialize (IHT1 _ Hlin1 H3) as (j & Π₀ & Hjfv & Hj & HH).
      exists j, Π₀. repeat split; auto.
      { simp term_fv. set_solver. }
      intros Γ. rewrite fill_app/=. f_equiv.
      * apply HH.
      * assert (j ∉ term_fv T2).
        { set_solver. }
        apply bterm_ctx_act_fv.
        intros i. destruct (decide (i = j)) as [->|?].
        { naive_solver. }
        rewrite fn_lookup_insert_ne//.
    + apply bunch_decomp_correct in H3.
      specialize (IHT2 _ Hlin2 H3) as (j & Π₀ & Hjfv & Hj & HH).
      exists j, Π₀. repeat split; auto.
      { simp term_fv. set_solver. }
      intros Γ. rewrite fill_app/=. f_equiv.
      * assert (j ∉ term_fv T1).
        { set_solver. }
        apply bterm_ctx_act_fv.
        intros i. destruct (decide (i = j)) as [->|?].
        { naive_solver. }
        rewrite fn_lookup_insert_ne//.
      * apply HH.
Qed.
