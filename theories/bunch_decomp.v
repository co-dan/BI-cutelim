(** Inductive representation for decomposition of bunches, and associated properties *)
From Coq Require Import ssreflect.
From stdpp Require Import prelude gmap functions.
From bunched Require Export syntax terms.

(** * Alternative representation of decomposition of bunches *)
(** We have an inductive type that characterizes when a bunch can be
  decomposed into a context and a sub-bunch. This essentially gives an
  us an inductive reasoning principle for equations [fill Π Δ = Δ']. *)
Inductive bunch_decomp {frml} :
  @bunch frml → @bunch_ctx frml → @bunch frml → Prop :=
| decomp_id Δ : bunch_decomp Δ [] Δ
| decomp_bin_1 sp Δ1 Δ2 Π Δ :
    bunch_decomp Δ1 Π Δ →
    bunch_decomp (bbin sp Δ1 Δ2) (Π ++ [CtxL sp Δ2]) Δ
| decomp_bin_2 sp Δ1 Δ2 Π Δ :
    bunch_decomp Δ2 Π Δ →
    bunch_decomp (bbin sp Δ1 Δ2) (Π ++ [CtxR sp Δ1]) Δ.

(** [bunch_decomp Δ' Π Δ] completely characterizes [fill Π Δ = Δ'] *)
Lemma bunch_decomp_correct {frml} (Δ Δ' : @bunch frml) Π :
  bunch_decomp Δ Π Δ' → Δ = fill Π Δ'.
Proof. induction 1; rewrite ?fill_app /= //; try by f_equiv. Qed.

Lemma bunch_decomp_complete' {frml} Π (Δ' : @bunch frml) :
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

Lemma bunch_decomp_complete {frml} (Δ Δ' : @bunch frml) Π :
  (fill Π Δ' = Δ) →
  bunch_decomp Δ Π Δ'.
Proof. intros <-. apply bunch_decomp_complete'. Qed.

Lemma bunch_decomp_iff {frml} (Δ Δ':@bunch frml) Π :
  (fill Π Δ' = Δ) ↔ bunch_decomp Δ Π Δ'.
Proof.
  split.
  - apply bunch_decomp_complete.
  - by symmetry; apply bunch_decomp_correct.
Qed.

(** * Properties of bunched contexts *)
(** We prove several useful properties using the inductive system defined above. *)

Lemma fill_is_frml {formula} Π Δ (ϕ : formula) :
  fill Π Δ = frml ϕ →
  Π = [] ∧ Δ = frml ϕ.
Proof.
  intros H%bunch_decomp_iff.
  inversion H; eauto.
Qed.

Lemma bunch_decomp_app {formula} Π Π0 (Δ Δ0 : @bunch formula) :
  bunch_decomp Δ Π0 Δ0 →
  bunch_decomp (fill Π Δ) (Π0 ++ Π) Δ0.
Proof.
  revert Δ Δ0 Π0.
  induction Π as [|F Π]=>Δ Δ0 Π0.
  { simpl. by rewrite app_nil_r. }
  intros HD.
  replace (Π0 ++ F :: Π) with ((Π0 ++ [F]) ++ Π); last first.
  { by rewrite -assoc. }
  apply IHΠ. destruct F; simpl; by econstructor.
Qed.

Lemma bunch_decomp_ctx {formula} Π Π' Δ (ϕ : formula) :
  bunch_decomp (fill Π Δ) Π' (frml ϕ) →
  ((∃ Π0, bunch_decomp Δ Π0 (frml ϕ) ∧ Π' = Π0 ++ Π) ∨
   (∃ (Π0 Π1 : bunch → bunch_ctx),
       (∀ Δ Δ', fill (Π0 Δ) Δ' = fill (Π1 Δ') Δ) ∧
       (∀ Δ', fill (Π1 Δ') Δ = fill Π' Δ') ∧
       (∀ A, bunch_decomp (fill Π A) (Π0 A) (frml ϕ)))).
Proof.
  revert Δ Π'.
  induction Π as [|F Π]=>Δ Π'; simpl.
  { remember (frml ϕ) as Γ1. intros Hdec.
    left. eexists. rewrite right_id. split; done. }
  simpl. intros Hdec.
  destruct (IHΠ _ _ Hdec) as [IH|IH].
  - destruct IH as [Π0 [HΠ0 HΠ]].
    destruct F; simpl in *.
    + inversion HΠ0; simplify_eq/=.
      * left. eexists; split; eauto.
        rewrite -assoc //.
      * right.
        exists (λ A, (Π1 ++ [CtxR s A]) ++ Π).
        exists (λ A, ([CtxL s (fill Π1 A)] ++ Π)).
        repeat split.
        { intros A B. by rewrite /= -!assoc /= !fill_app /=. }
        { intros A. by rewrite /= -!assoc /= !fill_app /=. }
        { intros A. apply bunch_decomp_app. by econstructor. }
    + inversion HΠ0; simplify_eq/=.
      * right.
        exists (λ A, (Π1 ++ [CtxL s A]) ++ Π).
        exists (λ A, ([CtxR s (fill Π1 A)] ++ Π)).
        repeat split.
        { intros A B. by rewrite /= -!assoc /= !fill_app. }
        { intros A. by rewrite /= -!assoc /= !fill_app. }
        { intros A. apply bunch_decomp_app. by econstructor. }
      * left. eexists; split; eauto.
        rewrite -assoc //.
  - right.
    destruct IH as (Π0 & Π1 & HΠ0 & HΠ1 & HΠ).
    exists (λ A, Π0 (fill_item F A)), (λ A, F::Π1 A). repeat split.
    { intros A B. simpl. rewrite -HΠ0 //. }
    { intros B. rewrite -HΠ1 //. }
    intros A. apply HΠ.
Qed.

Lemma bterm_ctx_act_decomp {formula} `{!EqDecision V, !Countable V} (T : bterm V)
  (Δs : V → bunch) (ϕ : formula) Π :
  linear_bterm T →
  bterm_ctx_act T Δs = fill Π (frml ϕ) →
  ∃ (j : V) Π₀ , j ∈ term_fv T ∧ Δs j = fill Π₀ (frml ϕ) ∧
   (∀ Δ, bterm_ctx_act T (<[j:=(fill Π₀ Δ)]>Δs) = fill Π Δ).
Proof.
  revert Π. induction T=>Π Hlin.
  - simpl.
    intros Hx. exists x, Π. repeat split; auto.
    { set_solver. }
    intros Γ. by rewrite fn_lookup_insert.
  - simpl. simpl in Hlin.
    destruct Hlin as (Ht12 & Hlin1 & Hlin2).
    intros Ht. symmetry in Ht.
    apply bunch_decomp_complete in Ht.
    inversion Ht; simplify_eq/=.
    + apply bunch_decomp_correct in H4.
      specialize (IHT1 _ Hlin1 H4) as (j & Π₀ & Hjfv & Hj & HH).
      exists j, Π₀. repeat split; auto.
      { simpl. set_solver. }
      intros Γ. rewrite fill_app/=. f_equiv.
      * apply HH.
      * assert (j ∉ term_fv T2).
        { set_solver. }
        apply bterm_ctx_act_fv.
        intros i. destruct (decide (i = j)) as [->|?].
        { naive_solver. }
        rewrite fn_lookup_insert_ne//.
    + apply bunch_decomp_correct in H4.
      specialize (IHT2 _ Hlin2 H4) as (j & Π₀ & Hjfv & Hj & HH).
      exists j, Π₀. repeat split; auto.
      { simpl. set_solver. }
      intros Γ. rewrite fill_app/=. f_equiv.
      * assert (j ∉ term_fv T1).
        { set_solver. }
        apply bterm_ctx_act_fv.
        intros i. destruct (decide (i = j)) as [->|?].
        { naive_solver. }
        rewrite fn_lookup_insert_ne//.
      * apply HH.
Qed.
