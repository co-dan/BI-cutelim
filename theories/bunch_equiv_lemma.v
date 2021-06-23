From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From iris_mod.bi Require Import bi.
From bunched Require Import seqcalc.

Module ALT_BE.

(** ** Alternative formulation of bunch equivalences *)
Inductive bunch_equiv : bunch → bunch → Type :=
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

Inductive bunch_equiv_h : bunch → bunch → Type :=
| h_refl x : bunch_equiv_h x x
| h_l_1 x y z : x =? y → bunch_equiv_h y z → bunch_equiv_h x z
| h_l_2 x y z : y =? x → bunch_equiv_h y z → bunch_equiv_h x z.

Lemma bunch_equiv_h_transitive x y z : bunch_equiv_h x y → bunch_equiv_h y z → bunch_equiv_h x z.
Proof.
  induction 1; eauto.
  - intros H1. eapply h_l_1; eauto.
  - intros H1. eapply h_l_2; eauto.
Defined.

Lemma bunch_equiv_once x y : x =? y → bunch_equiv_h x y.
Proof.
  intros Hq. eapply h_l_1; eauto. by constructor.
Defined.
Lemma bunch_equiv_once_2 x y : y =? x → bunch_equiv_h x y.
Proof.
  intros Hq. eapply h_l_2; eauto. by constructor.
Defined.
Lemma bunched_equiv_h_r_1 x y z : bunch_equiv_h x y → y =? z → bunch_equiv_h x z.
Proof.
  intros. eapply bunch_equiv_h_transitive; eauto.
  by apply bunch_equiv_once.
Defined.
Lemma bunched_equiv_h_r_2 x y z : bunch_equiv_h x y → z =? y → bunch_equiv_h x z.
Proof.
  intros. eapply bunch_equiv_h_transitive; eauto.
  by apply bunch_equiv_once_2.
Defined.

Lemma bunch_equiv_h_symmetric x y : bunch_equiv_h x y → bunch_equiv_h y x.
Proof.
  induction 1; first by constructor.
  - eapply bunched_equiv_h_r_2; eauto.
  - eapply bunched_equiv_h_r_1; eauto.
Defined.

Lemma bunch_equiv_1 Δ Δ' :
  (Δ =? Δ') → (seqcalc.bunch_equiv Δ Δ').
Proof. induction 1; by constructor. Defined.

Lemma bunch_equiv_2 Δ Δ' :
  (seqcalc.bunch_equiv Δ Δ') → (bunch_equiv_h Δ Δ').
Proof.
  induction 1.
  all: try by constructor.
  - by apply bunch_equiv_h_symmetric.
  - by eapply bunch_equiv_h_transitive.
  - clear H. induction IHbunch_equiv.
    + constructor.
    + eapply bunch_equiv_h_transitive; eauto.
      apply bunch_equiv_once. by apply BE_cong.
    + eapply bunch_equiv_h_transitive; eauto.
      apply bunch_equiv_once_2. by apply BE_cong.
  - apply bunch_equiv_once. apply BE_comma_unit_l.
  - apply bunch_equiv_once. apply BE_comma_comm.
  - apply bunch_equiv_once. apply BE_comma_assoc.
  - apply bunch_equiv_once. apply BE_semic_unit_l.
  - apply bunch_equiv_once. apply BE_semic_comm.
  - apply bunch_equiv_once. apply BE_semic_assoc.
Qed.

Local Lemma bunch_equiv_fill_1 Δ C ϕ :
  fill C (frml ϕ) =? Δ →
  { C' &
    ((Δ = fill C' (frml ϕ)) *
     (∀ Δ, seqcalc.bunch_equiv (fill C' Δ) (fill C Δ)))%type }.
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
      intros Δ. rewrite !fill_app.
      by apply seqcalc.BE_cong.
    * destruct H2 as ([C1 C2] & (Hdec & HC1) & HC2).
      specialize (Hdec Δ2). apply bunch_decomp_correct in Hdec.
      exists (C1 Δ2). split ; eauto.
      intros Δ. rewrite HC1.
      rewrite -HC2. apply seqcalc.BE_cong.
      apply BE_sym.
      by apply bunch_equiv_1.
  + apply bunch_decomp_complete in heqY.
    inversion heqY; simplify_eq/=.
    { inversion H3. }
    apply bunch_decomp_correct in H3.
    exists Π. split; eauto.
    intros X. rewrite fill_app /=.
    apply BE_sym. apply seqcalc.BE_comma_unit_l.
  + apply bunch_decomp_complete in heqY.
    inversion heqY; simplify_eq/=.
    * exists (Π ++ [CtxCommaR Δ2]). split.
      { rewrite fill_app/=.
        apply bunch_decomp_correct in H3.
        by rewrite H3. }
      intros Δ. rewrite !fill_app/=.
      apply seqcalc.BE_comma_comm.
    * exists (Π ++ [CtxCommaL Δ1]). split.
      { rewrite fill_app/=.
        apply bunch_decomp_correct in H3.
        by rewrite H3. }
      intros Δ. rewrite !fill_app/=.
      apply seqcalc.BE_comma_comm.
  + apply bunch_decomp_complete in heqY.
    inversion heqY; simplify_eq/=.
    * exists (Π ++ [CtxCommaL Δ2;CtxCommaL Δ3])%B. split.
      { rewrite fill_app/=.
        apply bunch_decomp_correct in H3.
        by rewrite H3. }
      intros Δ. rewrite !fill_app/=.
      apply BE_sym, seqcalc.BE_comma_assoc.
    * inversion H3; simplify_eq/=.
      ** exists (Π0 ++ [CtxCommaR Δ1;CtxCommaL Δ3])%B. split.
         { rewrite fill_app/=.
           apply bunch_decomp_correct in H4.
             by rewrite H4. }
         intros Δ. rewrite !fill_app/=.
         apply BE_sym, seqcalc.BE_comma_assoc.
      ** exists (Π0 ++ [CtxCommaR (Δ1,,Δ2)])%B. split.
         { simpl. rewrite fill_app/=.
           apply bunch_decomp_correct in H4.
           by rewrite H4. }
         intros Δ. rewrite !fill_app/=.
         apply BE_sym, seqcalc.BE_comma_assoc.
  + apply bunch_decomp_complete in heqY.
    inversion heqY; simplify_eq/=.
    { inversion H3. }
    apply bunch_decomp_correct in H3.
    exists Π. split; eauto.
    intros X. rewrite fill_app /=.
    apply BE_sym. apply seqcalc.BE_semic_unit_l.
  + apply bunch_decomp_complete in heqY.
    inversion heqY; simplify_eq/=.
    * exists (Π ++ [CtxSemicR Δ2]). split.
      { rewrite fill_app/=.
        apply bunch_decomp_correct in H3.
        by rewrite H3. }
      intros Δ. rewrite !fill_app/=.
      apply seqcalc.BE_semic_comm.
    * exists (Π ++ [CtxSemicL Δ1]). split.
      { rewrite fill_app/=.
        apply bunch_decomp_correct in H3.
        by rewrite H3. }
      intros Δ. rewrite !fill_app/=.
      apply seqcalc.BE_semic_comm.
  + apply bunch_decomp_complete in heqY.
    inversion heqY; simplify_eq/=.
    * exists (Π ++ [CtxSemicL Δ2;CtxSemicL Δ3])%B. split.
      { rewrite fill_app/=.
        apply bunch_decomp_correct in H3.
        by rewrite H3. }
      intros Δ. rewrite !fill_app/=.
      apply BE_sym, seqcalc.BE_semic_assoc.
    * inversion H3; simplify_eq/=.
      ** exists (Π0 ++ [CtxSemicR Δ1;CtxSemicL Δ3])%B. split.
         { rewrite fill_app/=.
           apply bunch_decomp_correct in H4.
             by rewrite H4. }
         intros Δ. rewrite !fill_app/=.
         apply BE_sym, seqcalc.BE_semic_assoc.
      ** exists (Π0 ++ [CtxSemicR (Δ1;,Δ2)])%B. split.
         { simpl. rewrite fill_app/=.
           apply bunch_decomp_correct in H4.
           by rewrite H4. }
         intros Δ. rewrite !fill_app/=.
         apply BE_sym, seqcalc.BE_semic_assoc.
Qed.

Local Lemma bunch_equiv_fill_2 Δ C ϕ :
  Δ =? fill C (frml ϕ) →
  { C' &
    ((Δ = fill C' (frml ϕ)) *
     (∀ Δ, seqcalc.bunch_equiv (fill C' Δ) (fill C Δ)))%type }.
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
      intros Δ. rewrite !fill_app.
      by apply seqcalc.BE_cong.
    * destruct H2 as ([C1 C2] & (Hdec & HC1) & HC2).
      specialize (Hdec Δ1). apply bunch_decomp_correct in Hdec.
      exists (C1 Δ1). split ; eauto.
      intros Δ. rewrite HC1.
      rewrite -HC2. apply seqcalc.BE_cong.
      by apply bunch_equiv_1.
  + exists (C' ++ [CtxCommaR empty]). simpl; split.
    { rewrite fill_app /=. by rewrite heqY. }
    intros X; rewrite fill_app/=.
    apply seqcalc.BE_comma_unit_l.
  + apply bunch_decomp_complete in heqY.
    inversion heqY; simplify_eq/=.
    * exists (Π ++ [CtxCommaR Δ1]). split.
      { rewrite fill_app/=.
        apply bunch_decomp_correct in H3.
        by rewrite H3. }
      intros Δ. rewrite !fill_app/=.
      apply seqcalc.BE_comma_comm.
    * exists (Π ++ [CtxCommaL Δ2]). split.
      { rewrite fill_app/=.
        apply bunch_decomp_correct in H3.
        by rewrite H3. }
      intros Δ. rewrite !fill_app/=.
      apply seqcalc.BE_comma_comm.
  + apply bunch_decomp_complete in heqY.
    inversion heqY; simplify_eq/=.
    * inversion H3; simplify_eq/=.
      ** exists (Π0 ++ [CtxCommaL (Δ2 ,, Δ3)])%B. split.
         { rewrite fill_app/=.
           apply bunch_decomp_correct in H4.
             by rewrite H4. }
         intros Δ. rewrite !fill_app/=.
         apply seqcalc.BE_comma_assoc.
      ** exists (Π0 ++ [CtxCommaL Δ3;CtxCommaR Δ1])%B. split.
         { simpl. rewrite fill_app/=.
           apply bunch_decomp_correct in H4.
           by rewrite H4. }
         intros Δ. rewrite !fill_app/=.
         apply seqcalc.BE_comma_assoc.
    * exists (Π ++ [CtxCommaR Δ2;CtxCommaR Δ1])%B. split.
      { rewrite fill_app/=.
        apply bunch_decomp_correct in H3.
          by rewrite H3. }
      intros Δ. rewrite !fill_app/=.
      apply seqcalc.BE_comma_assoc.
  + exists (C' ++ [CtxSemicR top]). simpl; split.
    { rewrite fill_app /=. by rewrite heqY. }
    intros X; rewrite fill_app/=.
    apply seqcalc.BE_semic_unit_l.
  + apply bunch_decomp_complete in heqY.
    inversion heqY; simplify_eq/=.
    * exists (Π ++ [CtxSemicR Δ1]). split.
      { rewrite fill_app/=.
        apply bunch_decomp_correct in H3.
        by rewrite H3. }
      intros Δ. rewrite !fill_app/=.
      apply seqcalc.BE_semic_comm.
    * exists (Π ++ [CtxSemicL Δ2]). split.
      { rewrite fill_app/=.
        apply bunch_decomp_correct in H3.
        by rewrite H3. }
      intros Δ. rewrite !fill_app/=.
      apply seqcalc.BE_semic_comm.
  + apply bunch_decomp_complete in heqY.
    inversion heqY; simplify_eq/=.
    * inversion H3; simplify_eq/=.
      ** exists (Π0 ++ [CtxSemicL (Δ2 ;, Δ3)])%B. split.
         { rewrite fill_app/=.
           apply bunch_decomp_correct in H4.
             by rewrite H4. }
         intros Δ. rewrite !fill_app/=.
         apply seqcalc.BE_semic_assoc.
      ** exists (Π0 ++ [CtxSemicL Δ3;CtxSemicR Δ1])%B. split.
         { simpl. rewrite fill_app/=.
           apply bunch_decomp_correct in H4.
           by rewrite H4. }
         intros Δ. rewrite !fill_app/=.
         apply seqcalc.BE_semic_assoc.
    * exists (Π ++ [CtxSemicR Δ2;CtxSemicR Δ1])%B. split.
      { rewrite fill_app/=.
        apply bunch_decomp_correct in H3.
          by rewrite H3. }
      intros Δ. rewrite !fill_app/=.
      apply seqcalc.BE_semic_assoc.
Qed.

Lemma rtc_rec_l (P : bunch → Type) (z : bunch)
      (Prefl : P z) (Pstep : ∀ x y, (x =? y) + (y =? x)
                                    → bunch_equiv_h y z → P y → P x) :
  ∀ x, bunch_equiv_h x z → P x.
Proof. induction 1; eauto. Defined.

End ALT_BE.

Lemma bunch_equiv_fill Δ C ϕ :
  seqcalc.bunch_equiv Δ (fill C (frml ϕ)) →
  { C' & ((Δ = fill C' (frml ϕ)) * (∀ Δ, seqcalc.bunch_equiv (fill C' Δ) (fill C Δ)) )%type }.
Proof.
  intros H%ALT_BE.bunch_equiv_2.
  revert Δ H. eapply ALT_BE.rtc_rec_l.
  { exists C. split; eauto.
    intros. apply BE_refl. }
  intros X Y HXY HY. clear HY.
  intros (C0 & -> & HC0).
  destruct HXY as [HXY|HXY].
  - apply ALT_BE.bunch_equiv_fill_2 in HXY.
    destruct HXY as (C' & -> & HC').
    eexists; split; eauto.
    intros Δ. eapply BE_trans; eauto.
  - apply ALT_BE.bunch_equiv_fill_1 in HXY.
    destruct HXY as (C' & -> & HC').
    eexists; split; eauto.
    intros Δ. eapply BE_trans; eauto.
Qed.
