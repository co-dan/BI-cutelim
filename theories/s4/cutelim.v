(* Semantic proof of cut elimination.. *)
From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From bunched.algebra Require Import bi from_monoid from_closure.
From bunched.s4 Require Import formula seqcalc_height seqcalc interp.
From bunched Require Import bunches.
Notation bunch := (@bunch formula).

#[global] Instance bunch_monoid : Monoid bunch (bbin Comma) :=
  {| monoid_unit := ∅ₘ%B |}.

Definition PB := PM bunch.
Canonical Structure PB_alg := PM_alg bunch (bbin Comma).

(** ** Principal closed sets *)
Program Definition Fint (ϕ : formula) : PB :=
  {| PMPred := (λ Δ, Δ ⊢ᴮ ϕ) |}.
Next Obligation. solve_proper. Qed.

Definition C := C bunch (bbin Comma) formula Fint.
Definition cl : PB → PB := cl bunch (bbin Comma) formula Fint.
Definition cl' : PB → C := cl' bunch (bbin Comma) formula Fint.

Definition CPred' : C → PB := CPred bunch (bbin Comma) formula Fint.
Coercion CPred' : C >-> PB.

Local Existing Instance C_equiv.

Definition Fint' (ϕ : formula) : C :=
  {| CPred := Fint ϕ |}.

(** * Baisc properties of C *)

Lemma C_inhabited (X : C) : (frml BOT) ∈ X.
Proof.
  destruct X as [X Xcl]. simpl.
  apply Xcl. intros ϕ Hϕ.
  eapply (BI_False_L []).
Qed.

(** An "introduction" rule for closed sets *)
Lemma C_intro (X : C) Δ :
  (∀ ϕ, ((X : PB) ⊢@{PB_alg} Fint ϕ) → Δ ⊢ᴮ ϕ) →
  Δ ∈ X.
Proof.
  destruct X as [X Xcl]. simpl.
  intros H1. by apply Xcl.
Qed.

Lemma C_weaken (X : C) Δ Δ' :
  Δ ∈ X → (Δ ;, Δ')%B ∈ X.
Proof.
  destruct X as [X Xcl]. simpl.
  intros HX. apply C_intro=> ϕ Hϕ.
  eapply (BI_Weaken []). simpl.
  by apply (Hϕ _).
Qed.

Lemma C_contract (X : C) Δ :
  (Δ ;, Δ)%B ∈ X → Δ ∈ X.
Proof.
  destruct X as [X Xcl]. simpl.
  intros HX. apply C_intro=> ϕ Hϕ.
  eapply (BI_Contr []). simpl.
  by apply (Hϕ _).
Qed.

Lemma C_collapse (X : C) Γ Δ :
  fill Γ Δ ∈ X → fill Γ (frml (collapse Δ)) ∈ X.
Proof.
  intros HX.
  apply C_intro=>ϕ Hϕ.
  apply BI_Collapse_L. by apply (Hϕ _).
Qed.

Lemma C_collapse_inv (X : C) Γ Δ :
  fill Γ (frml (collapse Δ)) ∈ X → fill Γ Δ ∈ X.
Proof.
  intros HX.
  apply C_intro=>ϕ Hϕ.
  apply BI_Collapse_L_inv. by apply (Hϕ _).
Qed.

(** Some calculations in the model. *)
Program Definition PB_and_alt (X Y : PB) :=
  MkPM bunch (λ Δ, ∃ Δ1 Δ2, (Δ ≡ (Δ1;,Δ2)%B) ∧
                              Δ1 ∈ X ∧ Δ2 ∈ Y) _.
Next Obligation. solve_proper. Qed.

Lemma C_and_eq (X Y : C) :
  ((X : PB) ∧ (Y : PB))%I ≡@{PB}
   cl (PB_and_alt (X : PB) (Y : PB)).
Proof.
  apply bi.equiv_entails; split.
  - intros Δ HΔ ϕ Hϕ.
    simpl. apply (BI_Contr [] Δ). simpl.
    apply (Hϕ _). exists Δ,Δ.
    split; eauto.
  - intros Δ HΔ. split.
    + apply C_intro=>ϕ Hϕ.
      eapply HΔ. clear HΔ Δ.
      intros Δ (Δ1 & Δ2 & -> & [H1 H2]). simpl.
      apply (BI_Weaken []). by apply (Hϕ _).
    + apply C_intro=>ϕ Hϕ.
      eapply HΔ. clear HΔ Δ.
      intros Δ (Δ1 & Δ2 & -> & [H1 H2]). simpl.
      rewrite comm.
      apply (BI_Weaken []). by apply (Hϕ _).
Qed.

Program Definition PB_impl_alt (X Y : PB) :=
  MkPM bunch (λ Δ, ∀ Δ', Δ' ∈ X → (Δ ;, Δ')%B ∈ Y) _.
Next Obligation.
  intros X Y Δ Δ2 Heq. split; repeat intro.
  - rewrite -Heq. naive_solver.
  - rewrite Heq. naive_solver.
Qed.

Lemma PB_impl_alt_adj (X : PB) (Y Z : C) :
  (PB_and_alt X (Y : PB) ⊢@{PB_alg} (Z : PB)) →
  (X ⊢ PB_impl_alt (Y : PB) (Z : PB)).
Proof.
  intros H1 Δ HX Δ' HY.
  apply (H1 _). do 2 eexists; eauto.
Qed.

(** * We show that cl is strong *)

Global Instance wand_is_closed (X : PB) (Y : C) :
  Is_closed Fint (X -∗ (Y : PB))%I.
Proof.
  apply Is_closed_inc.
  change (from_closure.cl bunch _ formula Fint) with cl.
  change (cl (X -∗ (Y : PB)) ⊢@{PB_alg} X -∗ (Y : PB)).
  cut (PM_forall _ ({ Δ | X Δ } * { ϕ : formula | (Y : PB) ⊢@{PB_alg} Fint ϕ })
               (λ '(Δ, ϕ), Fint' (WAND (collapse (`Δ)) (`ϕ)) : PB)
       ≡ (PM_wand _ _ X (Y : PB))%I).
  { intros <-. apply PM_forall_closed.
    intros. destruct x. apply _. }
  split.
  - intros Δ HXY Δ' HX.
    apply (C_collapse_inv _ [CtxCommaR Δ]).
    simpl.
    apply C_intro=>ϕ Hϕ.
    set (d1 := (Δ' ↾ HX) : {Δ : bunch | X Δ}).
    set (d2 := (ϕ ↾ Hϕ) : {ϕ : formula | (Y : PB) -∗ Fint ϕ}).
    specialize (HXY (d1, d2)). simpl in *.
    by apply wand_r_inv in HXY.
  - intros Δ HXY.
    intros ([Δ' HX], [ϕ Hϕ]).
    simpl. apply BI_Wand_R.
    apply (Hϕ _).
    apply (C_collapse _ [CtxCommaR Δ]).
    by apply (HXY _).
Qed.

Program Definition PB_impl' (X Y : PB) : PB :=
  {| PMPred := λ Δ, ∀ Δ', X Δ' → Y (Δ ;, Δ')%B |}.
Next Obligation.
  intros X Y D1 D2 H1. by setoid_rewrite H1.
Qed.

Global Instance PB_impl'_proper : Proper ((≡) ==> (≡) ==> (≡)) PB_impl'.
Proof. compute; naive_solver. Qed.

Global Instance PB_impl_Is_closed (X : PB) (Y : C) :
  Is_closed Fint (PB_impl' X (Y : PB)).
Proof.
  apply Is_closed_inc.
  change (from_closure.cl bunch _ formula Fint) with cl.
  (* change (cl (PB_impl' X Y) ⊢@{PB_alg} X → (Y : PB)). *)
  cut (PM_forall _ ({ Δ | X Δ } * { ϕ : formula | (Y : PB) ⊢@{PB_alg} Fint ϕ })
               (λ '(Δ, ϕ), Fint' (IMPL (collapse (`Δ)) (`ϕ)) : PB)
       ≡ (PB_impl' X Y)%I).
  { intros <-. apply PM_forall_closed.
    intros. destruct x. apply _. }
  split.
  - intros Δ HXY Δ' HX.
    apply (C_collapse_inv _ [CtxSemicR Δ]).
    simpl.
    apply C_intro=>ϕ Hϕ.
    set (d1 := (Δ' ↾ HX) : {Δ : bunch | X Δ}).
    set (d2 := (ϕ ↾ Hϕ) : {ϕ : formula | (Y : PB) -∗ Fint ϕ}).
    specialize (HXY (d1, d2)). simpl in *.
    by apply impl_r_inv in HXY.
  - intros Δ HXY.
    intros ([Δ' HX], [ϕ Hϕ]).
    simpl. apply BI_Impl_R.
    apply (Hϕ _).
    apply (C_collapse _ [CtxSemicR Δ]).
    by apply (HXY _).
Qed.


Program Definition C_impl (X Y : C) : C := {| CPred := PB_impl' X Y |}.

Lemma has_heyting_impl (X Y Z : C) :
  ((X : PB) ⊢@{PB_alg} ((C_impl Y Z) : PB)) ↔
      ((X : PB) ∧ (Y : PB) ⊢@{PB_alg} (Z : PB))%I.
Proof.
  rewrite C_and_eq.
  split.
  - intros H1. apply cl_adj; first apply _.
    intros Δ (Δ1 & Δ2 & -> & H2 & H3).
    by apply (H1 _).
  - intros H1.
    intros Δ1 H2 Δ2 H3. apply (H1 _).
    eapply (cl_unit _ _ _).
    eexists _,_. split; eauto.
Qed.

#[global] Instance C_impl_proper : Proper ((≡) ==> (≡) ==> (≡)) C_impl.
Proof.
  intros X1 X2 HX Y1 Y2 HY.
  unfold C_impl. split.
  - intros Δ. simpl. intros H1 Δ' HX'.
    apply HY. apply H1. apply HX. apply HX'.
  - intros Δ. simpl. intros H1 Δ' HX'.
    apply HY. apply H1. apply HX. apply HX'.
Qed.

Definition C_alg : bi :=
  C_alg bunch (bbin Comma) formula Fint C_impl C_impl_proper has_heyting_impl wand_is_closed.

(** * The Box modality *)
Program Definition PB_box (X: PB) : PB :=
  {| PMPred := λ Δ, ∃ Δ', Δ ≡ fmap BOX Δ' ∧ X Δ' |}.
Next Obligation. solve_proper. Qed.
Definition C_box (X : C) : C := cl' (PB_box X).

Lemma C_necessitate (X : C) Δ :
  Δ ∈ X → (fmap BOX Δ) ∈ X.
Proof.
  destruct X as [X Xcl]. simpl.
  intros HX. apply C_intro=> ϕ Hϕ.
  eapply (BI_Boxes_L []).
  by apply (Hϕ _).
Qed.

Lemma C_bunch_box_idemp (X : C) Δ :
  (fmap BOX (fmap BOX Δ)) ∈ X → (fmap BOX Δ) ∈ X.
Proof.
  destruct X as [X Xcl]. simpl.
  intros HX. apply C_intro=> ϕ Hϕ.
  eapply (box_l_inv []).
  by apply (Hϕ _).
Qed.

Lemma box_mono (P Q : C) : (P ⊢@{C_alg} Q) → C_box P ⊢@{C_alg} C_box Q.
Proof.
  intros HH. apply cl_mono.
  intros Δ. simpl. destruct 1 as (Δ' & HD & HP).
  exists Δ'. split; auto.
Qed.
Lemma box_elim (P : C) : C_box P ⊢@{C_alg} P.
Proof.
  apply cl_adj. { apply P. }
  intros Δ. simpl.
  destruct 1 as (Δ' & HD & HP). rewrite HD.
  by apply C_necessitate.
Qed.
Lemma box_idem P : C_box P ⊢@{C_alg} C_box (C_box P).
Proof.
  apply cl_adj. { apply _. }
  intros Δ.
  destruct 1 as (Δ' & HD & HP).
  rewrite HD.
  apply C_bunch_box_idemp.
  apply (cl_unit Fint _ _).
  eexists. split; eauto.
  apply (cl_unit Fint _ _).
  eexists. eauto.
Qed.

Lemma box_conj (P Q : C_alg) : C_box P ∧ C_box Q ⊢@{C_alg} C_box (P ∧ Q).
Proof.
  apply impl_elim_l'. apply cl_adj. { apply _. }
  intros Δ.
  destruct 1 as (Δ' & HD & HX).
  simpl. intros D1 H1 f Hf. rewrite HD.
  rewrite comm. apply (BI_Collapse_L_inv [CtxSemicR D1]). simpl.
  apply impl_r_inv. apply H1.
  intros D2. destruct 1 as (D2' & HD2 & HY). simpl.
  apply BI_Impl_R.
  apply (C_collapse (Fint' f) [CtxSemicR D2]). simpl.
  rewrite HD2.
  apply (Hf _). exists (D2';,Δ')%B. split.
  { simpl. done. }
  split.
  - rewrite comm. by apply C_weaken.
  - by apply C_weaken.
Qed.

Lemma box_sep (X Y : C_alg) : C_box X ∗ C_box Y ⊢@{C_alg} C_box (X ∗ Y).
Proof.
  apply bi.wand_elim_l'. apply cl'_adj.
  apply bi.wand_intro_r.
  rewrite comm.
  apply bi.wand_elim_l'.
  change ((C_box Y : PB) ⊢@{PB_alg} PB_box (X : C) -∗ (C_box (X ∗ Y) : PB)).
  apply cl_adj. { apply _. } apply bi.wand_intro_r.
  intros ? (Δ1 & Δ2 & (Θ1 & HT1 & HX) & (Θ2 & HT2 & HY) & ->).
  rewrite HT1 HT2. apply (cl_unit Fint _ _).
  exists (Θ1,, Θ2)%B. split; auto.
  apply (cl_unit _ _ _).
  do 2 eexists; repeat split; eauto.
  by rewrite comm.
Qed.

Lemma box_true : True ⊢@{C_alg} C_box (True : C_alg).
Proof.
  apply cl_adj. { apply _. } intros Δ _.
  rewrite -(BE_unit_l _ Δ).
  apply C_weaken. apply (cl_unit _ _ _).
  simpl. exists ∅ₐ%B. simpl. split; auto.
  apply (cl_unit _ _ _). done.
Qed.

Lemma box_emp : emp ⊢@{C_alg} C_box (emp : C_alg).
Proof.
  apply cl_mono. intros Δ HD; simpl.
  exists ∅ₘ%B. split; eauto. apply (cl_unit _ _ _).
  simpl. reflexivity.
Qed.

Global Instance C_alg_box : BiBox C_alg C_box.
Proof.
  split.
  - apply box_mono.
  - apply box_elim.
  - apply box_idem.
  - apply box_conj.
  - apply box_sep.
  - apply box_true.
  - apply box_emp.
Qed.

(** * Interpretation in [C] and Okada's lemma *)
Definition C_atom (a : atom) := Fint' (ATOM a).

Definition inner_interp : formula → C := @formula_interp C_alg C_box C_atom.

Lemma okada_property (A : formula) :
  (frml A ∈ inner_interp A)
   ∧ (inner_interp A ⊢@{C_alg} Fint' A).
Proof.
  induction A; simpl.
  - split; first by compute; eauto.
    intros Δ _. simpl. by constructor.
  - split.
    + compute. intros ϕ HΔ.
      eapply (BI_Emp_L []). by apply HΔ.
    + compute. intros Δ HΔ.
      apply HΔ. intros ? ->.
      by constructor.
  - split.
    + compute. intros ϕ H.
      apply (BI_False_L []).
    + compute. intros Δ H1.
      apply H1. naive_solver.
  - split; first by constructor.
    intros Δ. unfold C_atom. done.
  - destruct IHA1 as [IH11 IH12].
    destruct IHA2 as [IH21 IH22].
    split.
    + split.
      * apply (C_collapse _ [] (frml A1;, frml A2)%B). simpl.
        by apply C_weaken.
      * apply (C_collapse _ [] (frml A1;, frml A2)%B). simpl.
        rewrite comm.
        by apply C_weaken.
    + rewrite IH12 IH22.
      intros Δ. intros [H1 H2]. simpl.
      apply (BI_Contr []); simpl.
      apply BI_Conj_R; eauto.
  - destruct IHA1 as [IH11 IH12].
    destruct IHA2 as [IH21 IH22].
    split.
    + eapply C_intro=>ϕ Hϕ.
      apply (BI_Disj_L []); simpl.
      * eapply (Hϕ _). apply (cl_unit _ _ _).
        by left.
      * eapply (Hϕ _). apply (cl_unit _ _ _).
        by right.
    + rewrite IH12 IH22.
      apply bi.or_elim.
      * intros Δ HA1.
        simpl. apply BI_Disj_R1; eauto.
      * intros Δ HA2.
        simpl. apply BI_Disj_R2; eauto.
  - destruct IHA1 as [IH11 IH12].
    destruct IHA2 as [IH21 IH22].
    split.
    + apply (C_collapse _ [] (frml A1,, frml A2)%B); simpl. 
      apply (cl_unit _ _ _). exists (frml A1), (frml A2).
      repeat split; eauto.
    + rewrite IH12 IH22.
      apply cl'_adj.
      intros Δ (Δ1 & Δ2 & H1 & H2 & ->). simpl.
      apply BI_Sep_R; eauto.
  - destruct IHA1 as [IH11 IH12].
    destruct IHA2 as [IH21 IH22].
    split.
    + rewrite /bi_impl /= => Δ' HΔ'.
      apply C_intro=>ϕ Hϕ.
      rewrite comm.
      apply (BI_Impl_L []).
      { by apply (IH12 _). }
      simpl. by apply (Hϕ _).
    + intros Δ H1. simpl.
      constructor. apply (IH22 _).
      by apply (H1 _).
  - destruct IHA1 as [IH11 IH12].
    destruct IHA2 as [IH21 IH22].
    split.
    + move=> Δ' HΔ'.
      apply C_intro=>ϕ Hϕ.
      rewrite comm.
      apply (BI_Wand_L []).
      {  by apply (IH12 _). }
      simpl. by apply (Hϕ _).
    + intros Δ H1. simpl.
      constructor. apply (IH22 _).
      by apply (H1 _).
  - destruct IHA as [IH1 IH2].
    split.
    + intros ϕ Hϕ. apply (Hϕ _). simpl.
      exists (frml A). split; eauto.
    + apply cl_adj. { apply _. } intros ? (Δ & -> & HA).
      simpl. apply BI_Box_R. apply (IH2 _).
      by apply C_necessitate.
Qed.

Theorem C_interp_cf (Δ : bunch) (ϕ : formula) :
  seq_interp C_alg C_box C_atom Δ ϕ →
  (Δ ⊢ᴮ ϕ).
Proof.
  unfold seq_interp. intros H.
  destruct (okada_property ϕ) as [Hϕ1 Hϕ2].
  apply (Hϕ2 _). unfold inner_interp.
  apply (H _). apply (C_collapse_inv _ [] Δ). simpl.
  rewrite (bunch_interp_collapse C_alg _ C_atom).
  apply okada_property.
Qed.

Theorem cut Γ Δ ϕ ψ :
  (Δ ⊢ᴮ ψ) →
  (fill Γ (frml ψ) ⊢ᴮ ϕ) →
  fill Γ Δ ⊢ᴮ ϕ.
Proof.
  intros H1%(seq_interp_sound C_alg C_box C_atom).
  intros H2%(seq_interp_sound C_alg C_box C_atom).
  change (seq_interp _ _ _ Δ ψ) with (bunch_interp (formula_interp _ C_box C_atom) Δ ⊢@{C_alg} formula_interp _ C_box C_atom ψ) in H1.
  change (seq_interp _ _ _ (fill Γ (frml ψ)) ϕ) with
    (bunch_interp (formula_interp _ C_box C_atom) (fill Γ (frml ψ)) ⊢@{C_alg} formula_interp _ C_box C_atom ϕ) in H2.
  apply C_interp_cf.
  unfold seq_interp.
  etrans; last apply H2.
  apply bunch_interp_fill_mono.
  apply H1.
Qed.

(* Print Assumptions cut. *)
(*  ==> Closed under the global context *)
