(** Analytic completion of a structural rule *)
From Coq Require Import ssreflect.
From bunched.algebra Require Import bi.
From bunched Require Import syntax interp prelude.sets terms.
From stdpp Require Import prelude base gmap fin_sets.

Section analytic_completion.
  (** We start with an arbitrary structural rule [(Ts, T)] *)
  Variable (s : structural_rule).

  Definition ren_inverse : gmap nat (gset nat) := map_preimage (linearize_bterm_ren (snd s)).

  Definition transform_premise (Tz : bterm nat) : gset (bterm nat) :=
    let Tz_lin := linearize_bterm Tz in
    let r_Tz := linearize_bterm_ren Tz in
    let ren := λ j, ren_inverse !!! (r_Tz !!! j) in
    bterm_gset_fold $ ren <$> Tz_lin.

  Definition analytic_completion : structural_rule :=
    (mjoin $ fmap (elements ∘ transform_premise) (fst s), linearize_bterm (snd s)).
End analytic_completion.


(** Example: restricted form of weakening: [a ∗ a ≤ a]
    and it's analytic presentation [a₁ * a₂ ≤ a₁ ∨ a₂] *)

Example rule_restr_weakn : structural_rule := ([Var 0], TComma (Var 0) (Var 0)).
Example rule_restr_weakn_a := analytic_completion rule_restr_weakn.
Eval vm_compute in rule_restr_weakn_a.

Section analytic_completion_correct.
  Variable (s : structural_rule).
  Context {PROP : bi}.
  Implicit Type Xs Ys : nat → PROP.
  Implicit Type n k m : nat.

  Local Notation ren_inverse := (ren_inverse s).
  Local Notation transform_premise := (transform_premise s).
  Local Notation T := (snd s).
  Local Notation Ts := (fst s).

  Definition disj_ren_inverse Xs : nat → PROP := λ n, (∃ k, ⌜k ∈ ren_inverse !!! n⌝ ∧ Xs k)%I.

  Definition linearize_bterm_ren_act Xs : nat → PROP :=
    λ (n : nat), Xs (linearize_bterm_ren T !!! n).

  Lemma ren_ren_inverse i j :
    j ∈ ren_inverse !!! i → linearize_bterm_ren T !!! j = i.
  Proof.
    rewrite /ren_inverse. rewrite lookup_total_preimage.
    apply lookup_total_correct.
  Qed.

  Lemma linearize_bterm_act Xs :
    bterm_alg_act (linearize_bterm T) Xs ⊢ bterm_alg_act T (disj_ren_inverse Xs).
  Proof.
    rewrite /disj_ren_inverse /ren_inverse /linearize_bterm_ren /linearize_bterm.
    generalize 0.
    induction T as [x | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 ]=>i; simpl.
    - apply (bi.exist_intro' _ _ i).
      rewrite map_preimage_singleton.
      apply bi.and_intro; eauto. apply bi.pure_intro. rewrite lookup_total_singleton. set_solver.
    - specialize (IHT1 i).
      destruct (linearize_pre T1 i) as [[i1 m1] T1'] eqn:Ht1.
      specialize (IHT2 i1).
      destruct (linearize_pre T2 i1) as [[i2 m2] T2'] eqn:Ht2. simpl.
      assert (dom (gset _) m1 = set_seq i (i1-i)) as Hm1.
      { replace i1 with (fst $ fst (linearize_pre T1 i)) by rewrite Ht1 //.
        replace m1 with (snd $ fst (linearize_pre T1 i)) by rewrite Ht1 //.
        apply linearize_pre_dom. }
      assert (dom (gset _) m2 = set_seq i1 (i2-i1)) as Hm2.
      { replace i2 with (fst $ fst (linearize_pre T2 i1)) by rewrite Ht2 //.
        replace m2 with (snd $ fst (linearize_pre T2 i1)) by rewrite Ht2 //.
        apply linearize_pre_dom. }
      assert (m1 ##ₘ m2) as Hm1m2disj.
      { apply map_disjoint_dom_2. rewrite Hm1 Hm2.
        set_unfold. lia. }
      f_equiv.
      { rewrite IHT1 /=.
        apply bterm_alg_act_mono=>j.
        apply bi.exist_mono'=>k. do 2 f_equiv.
        rewrite !lookup_total_preimage.
        intro. by apply lookup_union_Some_l. }
      { rewrite IHT2 /=.
        apply bterm_alg_act_mono=>j.
        apply bi.exist_mono'=>k. do 2 f_equiv.
        rewrite !lookup_total_preimage.
        intro. by apply lookup_union_Some_r. }
    - specialize (IHT1 i).
      destruct (linearize_pre T1 i) as [[i1 m1] T1'] eqn:Ht1.
      specialize (IHT2 i1).
      destruct (linearize_pre T2 i1) as [[i2 m2] T2'] eqn:Ht2. simpl.
      assert (dom (gset _) m1 = set_seq i (i1-i)) as Hm1.
      { replace i1 with (fst $ fst (linearize_pre T1 i)) by rewrite Ht1 //.
        replace m1 with (snd $ fst (linearize_pre T1 i)) by rewrite Ht1 //.
        apply linearize_pre_dom. }
      assert (dom (gset _) m2 = set_seq i1 (i2-i1)) as Hm2.
      { replace i2 with (fst $ fst (linearize_pre T2 i1)) by rewrite Ht2 //.
        replace m2 with (snd $ fst (linearize_pre T2 i1)) by rewrite Ht2 //.
        apply linearize_pre_dom. }
      assert (m1 ##ₘ m2) as Hm1m2disj.
      { apply map_disjoint_dom_2. rewrite Hm1 Hm2.
        set_unfold. lia. }
      f_equiv.
      { rewrite IHT1 /=.
        apply bterm_alg_act_mono=>j.
        apply bi.exist_mono'=>k. do 2 f_equiv.
        rewrite !lookup_total_preimage. intro. by apply lookup_union_Some_l. }
      { rewrite IHT2 /=.
        apply bterm_alg_act_mono=>j.
        apply bi.exist_mono'=>k. do 2 f_equiv.
        rewrite !lookup_total_preimage. intro. by apply lookup_union_Some_r. }
  Qed.

  Lemma bterm_alg_act_renaming'' Tz Xs :
    bterm_alg_act Tz (linearize_bterm_ren_act Xs) ≡ bterm_alg_act ((λ n, linearize_bterm_ren T !!! n) <$> Tz) Xs.
  Proof.
    rewrite /linearize_bterm_ren_act.
    induction Tz as [x | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 ]; eauto; simpl; by f_equiv.
  Qed.

  Lemma bterm_alg_act_disj_ren_inverse_transform Tz Xs :
    bterm_alg_act Tz (disj_ren_inverse Xs) -∗ ∃ Tk, ⌜Tk ∈ transform_premise Tz⌝ ∧ bterm_alg_act Tk Xs.
  Proof.
    rewrite /disj_ren_inverse /transform_premise /linearize_bterm /linearize_bterm_ren.
    generalize 0.
    induction Tz as [x | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 ]=>idx; simpl.
    - apply bi.exist_elim=>k. apply bi.pure_elim_l=>Hk.
      apply (bi.exist_intro' _ _ (Var k)). apply bi.and_intro; eauto.
      apply bi.pure_intro. eapply elem_of_map_2. by rewrite lookup_total_singleton.
    - specialize (IHT1 idx).
      destruct (linearize_pre T1 idx) as [[idx1 m1] T1'] eqn:Ht1.
      specialize (IHT2 idx1).
      destruct (linearize_pre T2 idx1) as [[idx2 m2] T2'] eqn:Ht2.

      assert (dom (gset _) m1 = set_seq idx (idx1-idx)) as Hm1.
      { replace idx1 with (fst $ fst (linearize_pre T1 idx)) by rewrite Ht1 //.
        replace m1 with (snd $ fst (linearize_pre T1 idx)) by rewrite Ht1 //.
        apply linearize_pre_dom. }
      assert (dom (gset _) m2 = set_seq idx1 (idx2-idx1)) as Hm2.
      { replace idx2 with (fst $ fst (linearize_pre T2 idx1)) by rewrite Ht2 //.
        replace m2 with (snd $ fst (linearize_pre T2 idx1)) by rewrite Ht2 //.
        apply linearize_pre_dom. }
      assert (m1 ##ₘ m2) as Hm1m2disj.
      { apply map_disjoint_dom_2. rewrite Hm1 Hm2.
        set_unfold. lia. }

      assert (term_fv T1' ⊆ set_seq idx (idx1-idx)) as Hfv1.
      { replace T1' with (snd (linearize_pre T1 idx)) by rewrite Ht1 //.
        replace idx1 with (fst $ fst (linearize_pre T1 idx)) by rewrite Ht1 //.
        apply linearize_pre_fv. }
      assert (term_fv T2' ⊆ set_seq idx1 (idx2-idx1)) as Hfv2.
      { replace T2' with (snd (linearize_pre T2 idx1)) by rewrite Ht2 //.
        replace idx2 with (fst $ fst (linearize_pre T2 idx1)) by rewrite Ht2 //.
        apply linearize_pre_fv. }

      rewrite IHT1 . rewrite bi.sep_exist_r. apply bi.exist_elim=>Tk1.
      rewrite bi.sep_and_r. rewrite bi.pure_sep_l.
      apply bi.pure_elim_l=>Hk1.
      rewrite IHT2. rewrite comm. rewrite bi.sep_exist_r. apply bi.exist_elim=>Tk2.
      rewrite bi.sep_and_r. rewrite bi.pure_sep_l.
      apply bi.pure_elim_l=>Hk2. rewrite comm.
      apply (bi.exist_intro' _ _ (TComma Tk1 Tk2)). apply bi.and_intro; simpl; last by f_equiv.
      apply bi.pure_intro.
      apply sets.elem_of_set_map_2. eexists _,_. repeat split; eauto.
      + simpl in Hk1.
        enough ((λ j : nat, ren_inverse !!! (m1 !!! j)) <$> T1' = ((λ j : nat, ren_inverse !!! ((m1 ∪ m2) !!! j)) <$> T1'))
          as <-; first done.
        apply bterm_fmap_ext; last done. intros x Hx. f_equiv.
        rewrite !lookup_total_alt. f_equiv.
        symmetry. apply lookup_union_l. apply elem_of_dom.
        set_unfold. naive_solver.
      + simpl in Hk2.
        enough ((λ j : nat, ren_inverse !!! (m2 !!! j)) <$> T2' = ((λ j : nat, ren_inverse !!! ((m1 ∪ m2) !!! j)) <$> T2'))
          as <-; first done.
        apply bterm_fmap_ext; last done. intros x Hx. f_equiv.
        rewrite !lookup_total_alt. f_equiv.
        symmetry. apply lookup_union_r. apply not_elem_of_dom.
        set_unfold. intros Hx'. apply Hfv2 in Hx. apply Hm1 in Hx'. lia.
    - specialize (IHT1 idx).
      destruct (linearize_pre T1 idx) as [[idx1 m1] T1'] eqn:Ht1.
      specialize (IHT2 idx1).
      destruct (linearize_pre T2 idx1) as [[idx2 m2] T2'] eqn:Ht2.

      assert (dom (gset _) m1 = set_seq idx (idx1-idx)) as Hm1.
      { replace idx1 with (fst $ fst (linearize_pre T1 idx)) by rewrite Ht1 //.
        replace m1 with (snd $ fst (linearize_pre T1 idx)) by rewrite Ht1 //.
        apply linearize_pre_dom. }
      assert (dom (gset _) m2 = set_seq idx1 (idx2-idx1)) as Hm2.
      { replace idx2 with (fst $ fst (linearize_pre T2 idx1)) by rewrite Ht2 //.
        replace m2 with (snd $ fst (linearize_pre T2 idx1)) by rewrite Ht2 //.
        apply linearize_pre_dom. }
      assert (m1 ##ₘ m2) as Hm1m2disj.
      { apply map_disjoint_dom_2. rewrite Hm1 Hm2.
        set_unfold. lia. }

      assert (term_fv T1' ⊆ set_seq idx (idx1-idx)) as Hfv1.
      { replace T1' with (snd (linearize_pre T1 idx)) by rewrite Ht1 //.
        replace idx1 with (fst $ fst (linearize_pre T1 idx)) by rewrite Ht1 //.
        apply linearize_pre_fv. }
      assert (term_fv T2' ⊆ set_seq idx1 (idx2-idx1)) as Hfv2.
      { replace T2' with (snd (linearize_pre T2 idx1)) by rewrite Ht2 //.
        replace idx2 with (fst $ fst (linearize_pre T2 idx1)) by rewrite Ht2 //.
        apply linearize_pre_fv. }

      rewrite IHT1. rewrite bi.and_exist_r. apply bi.exist_elim=>Tk1.
      rewrite -assoc.
      apply bi.pure_elim_l=>Hk1.
      rewrite IHT2. rewrite comm. rewrite bi.and_exist_r. apply bi.exist_elim=>Tk2.
      rewrite -assoc.
      apply bi.pure_elim_l=>Hk2. rewrite comm.
      apply (bi.exist_intro' _ _ (TSemic Tk1 Tk2)). apply bi.and_intro; simpl; last by f_equiv.
      apply bi.pure_intro.
      apply sets.elem_of_set_map_2. eexists _,_. repeat split; eauto.
      + simpl in Hk1.
        enough ((λ j : nat, ren_inverse !!! (m1 !!! j)) <$> T1' = ((λ j : nat, ren_inverse !!! ((m1 ∪ m2) !!! j)) <$> T1'))
          as <-; first done.
        apply bterm_fmap_ext; last done. intros x Hx. f_equiv.
        rewrite !lookup_total_alt. f_equiv.
        symmetry. apply lookup_union_l. apply elem_of_dom.
        set_unfold. naive_solver.
      + simpl in Hk2.
        enough ((λ j : nat, ren_inverse !!! (m2 !!! j)) <$> T2' = ((λ j : nat, ren_inverse !!! ((m1 ∪ m2) !!! j)) <$> T2'))
          as <-; first done.
        apply bterm_fmap_ext; last done. intros x Hx. f_equiv.
        rewrite !lookup_total_alt. f_equiv.
        symmetry. apply lookup_union_r. apply not_elem_of_dom.
        set_unfold. intros Hx'. apply Hfv2 in Hx. apply Hm1 in Hx'. lia.
  Qed.

  Lemma elem_of_map_ren_ren_inverse x y :
    y ∈ (set_map (C:=gset nat) (λ n, linearize_bterm_ren T !!! n) (ren_inverse !!! x) : gset nat) → y = x.
  Proof.
    rewrite elem_of_map.
    intros [z [-> Hz]]. by apply ren_ren_inverse.
  Qed.

  Lemma transformed_premise_act_ren Tz' Tz Xs :
    Tz' ∈ transform_premise Tz → bterm_alg_act Tz' (linearize_bterm_ren_act Xs) ≡ bterm_alg_act Tz Xs.
  Proof.
    rewrite /transform_premise.
    intros H1.
    apply (bterm_gset_fold_fmap (λ n, linearize_bterm_ren T !!! n)) in H1.
    revert H1.
    rewrite /bterm_gset_fmap.
    rewrite -(bterm_fmap_compose (λ j : nat, ren_inverse !!! (linearize_bterm_ren Tz !!! j))).
    rewrite bterm_alg_act_renaming''.
    intros H1. f_equiv.
    revert H1.
    pose (Tz'' := (λ n, linearize_bterm_ren T !!! n) <$> Tz').
    fold Tz''. intros HTz''.
    assert (Tz'' ∈ bterm_gset_fold
                ((λ j : nat, set_map (λ n, linearize_bterm_ren T !!! n) (ren_inverse !!! (linearize_bterm_ren Tz !!! j))) <$> linearize_bterm Tz)) as HH.
    {  apply HTz''. }
    clear HTz''.
    apply bterm_gset_fold_fmap_inv in HH; last first.
    { apply linearize_pre_linear. }
    destruct HH as [g [Hg ->]].
    assert (∀ i : nat,
           i ∈ term_fv (linearize_bterm Tz)
         → g i = (linearize_bterm_ren Tz !!! i)) as HHH.
    { intros i Hi. apply elem_of_map_ren_ren_inverse.
      by eapply Hg. }
    clear Hg. revert HHH.
    rewrite /(linearize_bterm_ren Tz) /(linearize_bterm Tz).
    generalize 0.
    induction Tz as [x | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 ]=>i; simpl.
    - intros H1. f_equiv.
      etrans. { apply H1. by apply elem_of_singleton. }
      apply lookup_total_singleton.
    - intros H1.
      specialize (IHT1 i).
      destruct (linearize_pre T1 i) as [[i1 m1] T1'] eqn:Ht1.
      specialize (IHT2 i1).
      destruct (linearize_pre T2 i1) as [[i2 m2] T2'] eqn:Ht2.
      assert (term_fv T1' ⊆ set_seq i (i1-i)).
      { replace T1' with (snd (linearize_pre T1 i)) by rewrite Ht1 //.
        replace i1 with (fst $ fst (linearize_pre T1 i)) by rewrite Ht1 //.
        apply linearize_pre_fv. }
      assert (term_fv T2' ⊆ set_seq i1 (i2-i1)).
      { replace T2' with (snd (linearize_pre T2 i1)) by rewrite Ht2 //.
        replace i2 with (fst $ fst (linearize_pre T2 i1)) by rewrite Ht2 //.
        apply linearize_pre_fv. }
      assert (dom (gset _) m1 = set_seq i (i1-i)) as Hm1.
      { replace i1 with (fst $ fst (linearize_pre T1 i)) by rewrite Ht1 //.
        replace m1 with (snd $ fst (linearize_pre T1 i)) by rewrite Ht1 //.
        apply linearize_pre_dom. }
      assert (dom (gset _) m2 = set_seq i1 (i2-i1)) as Hm2.
      { replace i2 with (fst $ fst (linearize_pre T2 i1)) by rewrite Ht2 //.
        replace m2 with (snd $ fst (linearize_pre T2 i1)) by rewrite Ht2 //.
        apply linearize_pre_dom. }
      simpl. f_equiv.
      { apply IHT1. intros j Hj. simpl in *. trans ((m1 ∪ m2) !!! j).
        - apply H1. set_solver.
        - rewrite !lookup_total_alt. f_equiv.
          apply lookup_union_l.
          apply elem_of_dom. rewrite Hm1. naive_solver. }
      { apply IHT2. intros j Hj. simpl in *. trans ((m1 ∪ m2) !!! j).
        - apply H1. set_solver.
        - rewrite !lookup_total_alt. f_equiv.
          apply lookup_union_r. apply not_elem_of_dom.
          rewrite Hm1. set_unfold. naive_solver lia. }
    - intros H1.
      specialize (IHT1 i).
      destruct (linearize_pre T1 i) as [[i1 m1] T1'] eqn:Ht1.
      specialize (IHT2 i1).
      destruct (linearize_pre T2 i1) as [[i2 m2] T2'] eqn:Ht2.
      assert (term_fv T1' ⊆ set_seq i (i1-i)).
      { replace T1' with (snd (linearize_pre T1 i)) by rewrite Ht1 //.
        replace i1 with (fst $ fst (linearize_pre T1 i)) by rewrite Ht1 //.
        apply linearize_pre_fv. }
      assert (term_fv T2' ⊆ set_seq i1 (i2-i1)).
      { replace T2' with (snd (linearize_pre T2 i1)) by rewrite Ht2 //.
        replace i2 with (fst $ fst (linearize_pre T2 i1)) by rewrite Ht2 //.
        apply linearize_pre_fv. }
      assert (dom (gset _) m1 = set_seq i (i1-i)) as Hm1.
      { replace i1 with (fst $ fst (linearize_pre T1 i)) by rewrite Ht1 //.
        replace m1 with (snd $ fst (linearize_pre T1 i)) by rewrite Ht1 //.
        apply linearize_pre_dom. }
      assert (dom (gset _) m2 = set_seq i1 (i2-i1)) as Hm2.
      { replace i2 with (fst $ fst (linearize_pre T2 i1)) by rewrite Ht2 //.
        replace m2 with (snd $ fst (linearize_pre T2 i1)) by rewrite Ht2 //.
        apply linearize_pre_dom. }
      simpl. f_equiv.
      { apply IHT1. intros j Hj. simpl in *. trans ((m1 ∪ m2) !!! j).
        - apply H1. set_solver.
        - rewrite !lookup_total_alt. f_equiv.
          apply lookup_union_l.
          apply elem_of_dom. rewrite Hm1. naive_solver. }
      { apply IHT2. intros j Hj. simpl in *. trans ((m1 ∪ m2) !!! j).
        - apply H1. set_solver.
        - rewrite !lookup_total_alt. f_equiv.
          apply lookup_union_r. apply not_elem_of_dom.
          rewrite Hm1. set_unfold. naive_solver lia. }
  Qed.

  Lemma linearize_bterm_act_ren Xs:
    bterm_alg_act (linearize_bterm T) (linearize_bterm_ren_act Xs) ≡ bterm_alg_act T Xs.
  Proof.
    rewrite /linearize_bterm_ren_act /linearize_bterm_ren /linearize_bterm.
    generalize 0.
    induction T as [x | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 ]=>i; simpl.
    - by rewrite lookup_total_singleton.
    - specialize (IHT1 i).
      destruct (linearize_pre T1 i) as [[i1 m1] T1'] eqn:Ht1.
      specialize (IHT2 i1).
      destruct (linearize_pre T2 i1) as [[i2 m2] T2'] eqn:Ht2.
      assert (term_fv T1' ⊆ set_seq i (i1-i)).
      { replace T1' with (snd (linearize_pre T1 i)) by rewrite Ht1 //.
        replace i1 with (fst $ fst (linearize_pre T1 i)) by rewrite Ht1 //.
        apply linearize_pre_fv. }
      assert (term_fv T2' ⊆ set_seq i1 (i2-i1)).
      { replace T2' with (snd (linearize_pre T2 i1)) by rewrite Ht2 //.
        replace i2 with (fst $ fst (linearize_pre T2 i1)) by rewrite Ht2 //.
        apply linearize_pre_fv. }
      assert (dom (gset _) m1 = set_seq i (i1-i)) as Hm1.
      { replace i1 with (fst $ fst (linearize_pre T1 i)) by rewrite Ht1 //.
        replace m1 with (snd $ fst (linearize_pre T1 i)) by rewrite Ht1 //.
        apply linearize_pre_dom. }
      assert (dom (gset _) m2 = set_seq i1 (i2-i1)) as Hm2.
      { replace i2 with (fst $ fst (linearize_pre T2 i1)) by rewrite Ht2 //.
        replace m2 with (snd $ fst (linearize_pre T2 i1)) by rewrite Ht2 //.
        apply linearize_pre_dom. }
      simpl. repeat split; eauto.
      rewrite -IHT1 -IHT2. f_equiv.
      + eapply bterm_alg_act_fv.
        intros j Hj.
        assert ((m1 ∪ m2) !!! j = m1 !!! j) as ->; eauto.
        unfold lookup_total, map_lookup_total. f_equiv.
        apply lookup_union_l, elem_of_dom. rewrite Hm1. set_solver by lia.
      + eapply bterm_alg_act_fv.
        intros j Hj.
        assert ((m1 ∪ m2) !!! j = m2 !!! j) as ->; eauto.
        unfold lookup_total, map_lookup_total. f_equiv.
        apply lookup_union_r. apply not_elem_of_dom. rewrite Hm1. set_solver by lia.
    - specialize (IHT1 i).
      destruct (linearize_pre T1 i) as [[i1 m1] T1'] eqn:Ht1.
      specialize (IHT2 i1).
      destruct (linearize_pre T2 i1) as [[i2 m2] T2'] eqn:Ht2.
      assert (term_fv T1' ⊆ set_seq i (i1-i)).
      { replace T1' with (snd (linearize_pre T1 i)) by rewrite Ht1 //.
        replace i1 with (fst $ fst (linearize_pre T1 i)) by rewrite Ht1 //.
        apply linearize_pre_fv. }
      assert (term_fv T2' ⊆ set_seq i1 (i2-i1)).
      { replace T2' with (snd (linearize_pre T2 i1)) by rewrite Ht2 //.
        replace i2 with (fst $ fst (linearize_pre T2 i1)) by rewrite Ht2 //.
        apply linearize_pre_fv. }
      assert (dom (gset _) m1 = set_seq i (i1-i)) as Hm1.
      { replace i1 with (fst $ fst (linearize_pre T1 i)) by rewrite Ht1 //.
        replace m1 with (snd $ fst (linearize_pre T1 i)) by rewrite Ht1 //.
        apply linearize_pre_dom. }
      assert (dom (gset _) m2 = set_seq i1 (i2-i1)) as Hm2.
      { replace i2 with (fst $ fst (linearize_pre T2 i1)) by rewrite Ht2 //.
        replace m2 with (snd $ fst (linearize_pre T2 i1)) by rewrite Ht2 //.
        apply linearize_pre_dom. }
      simpl. repeat split; eauto.
      rewrite -IHT1 -IHT2. f_equiv.
      + eapply bterm_alg_act_fv.
        intros j Hj.
        assert ((m1 ∪ m2) !!! j = m1 !!! j) as ->; eauto.
        unfold lookup_total, map_lookup_total. f_equiv.
        apply lookup_union_l, elem_of_dom. rewrite Hm1. set_solver by lia.
      + eapply bterm_alg_act_fv.
        intros j Hj.
        assert ((m1 ∪ m2) !!! j = m2 !!! j) as ->; eauto.
        unfold lookup_total, map_lookup_total. f_equiv.
        apply lookup_union_r. apply not_elem_of_dom. rewrite Hm1. set_solver by lia.
  Qed.

End analytic_completion_correct.

Lemma analytic_completion_sound (s : structural_rule) (PROP : bi) :
  rule_valid (analytic_completion s) PROP → rule_valid s PROP.
Proof.
  rewrite /rule_valid /=.
  set (T := snd s).
  set (Ts := fst s).
  intros H1 Xs.
  rewrite - linearize_bterm_act_ren.
  rewrite H1. apply bi.exist_elim=>Ti.
  destruct Ti as [Ti HTi]. simpl.
  apply elem_of_list_join in HTi.
  destruct HTi as [L [HTi HL]].
  apply elem_of_list_fmap_2 in HL.
  destruct HL as [Tz [-> HTz]].
  apply (bi.exist_intro' _ _  (Tz ↾ HTz)).
  simpl in *. apply elem_of_elements in HTi.
  eapply transformed_premise_act_ren in HTi.
  by rewrite HTi.
Qed.

Lemma analytic_completion_complete (s : structural_rule) (PROP : bi) :
  rule_valid s PROP → rule_valid (analytic_completion s) PROP.
Proof.
  rewrite /rule_valid /=.
  set (T := snd s).
  set (Ts := fst s).
  intros H1 Xs.
  rewrite linearize_bterm_act.
  rewrite H1. apply bi.exist_elim=>Ti.
  destruct Ti as [Ti HTi]. simpl.
  rewrite bterm_alg_act_disj_ren_inverse_transform.
  apply bi.exist_elim=>Tk. apply bi.pure_elim_l=>Htk.
  assert (Tk ∈ mjoin (fmap (elements ∘ transform_premise s) Ts)) as Tk'.
  { apply elem_of_list_join. exists (elements (transform_premise s Ti)).
    split.
    - by apply elem_of_elements.
    - rewrite list_fmap_compose.
      by do 2 apply elem_of_list_fmap_1. }
  apply (bi.exist_intro' _ _  (Tk ↾ Tk')); done.
Qed.
