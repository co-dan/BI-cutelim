(* Semantic proof of cut elimination.. *)
From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From bunched.algebra Require Import bi.
From bunched Require Import seqcalc_height_s4 seqcalc_s4 interp_s4.

(** The first algebra that we consider is a purely "combinatorial" one:
    predicates [(bunch/≡) → Prop] *)
Module PB.

  Record PB := MkPB {
    PBPred :> bunch → Prop;
    PBPred_proper : Proper ((≡) ==> (iff)) PBPred;
  }.
  Arguments MkPB _%B {_}.
  Global Existing Instance PBPred_proper.

  Global Instance PB_equiv : Equiv PB := λ X Y,
     (∀ Δ, X Δ ↔ Y Δ).
  Global Instance PB_equiv_equivalence : Equivalence (≡@{PB}).
  Proof.
    rewrite /equiv /PB_equiv.
    split; repeat intro; naive_solver.
  Qed.

  Definition PB_entails (X Y : PB) : Prop :=
    ∀ Δ, X Δ → Y Δ.

  Program Definition PB_and (X Y : PB) : PB :=
    {| PBPred := (λ Δ, X Δ ∧ Y Δ) |}.
  Next Obligation. solve_proper. Qed.

  Program Definition PB_impl (X Y : PB) : PB :=
    {| PBPred := (λ Δ, X Δ → Y Δ) |}.
  Next Obligation.
    intros X Y Δ Δ' HΔ. rewrite HΔ.
    eauto.
  Qed.

  Program Definition PB_emp : PB :=
    {| PBPred := (λ Δ, Δ ≡ empty) |}.
  Next Obligation. solve_proper. Qed.

  Program Definition PB_sep (X Y : PB) : PB :=
    {| PBPred := (λ Δ, ∃ Δ1 Δ2, X Δ1 ∧ Y Δ2 ∧ (Δ ≡ (Δ1 ,, Δ2)%B)) |}.
  Next Obligation. solve_proper. Qed.

  Program Definition PB_wand (X Y : PB) : PB :=
    @MkPB (λ Δ, ∀ Δ1, X Δ1 → Y (Δ ,, Δ1)%B) _.
  Next Obligation.
    intros X Y Δ Δ' HΔ. by setoid_rewrite HΔ.
  Qed.

  Definition PB_pure (ϕ : Prop) : PB := MkPB (λ _, ϕ).

  Program Definition PB_or (X Y : PB) : PB :=
    {| PBPred := (λ Δ, X Δ ∨ Y Δ)%B |}.
  Next Obligation. solve_proper. Qed.

  Program Definition PB_forall (A : Type) (DD : A → PB) : PB :=
    @MkPB (λ Δ, ∀ (a : A), DD a Δ) _.
  Next Obligation.
    intros A DD Δ Δ' HΔ. by setoid_rewrite HΔ.
  Qed.

  Program Definition PB_exists (A : Type) (PBPB : A → PB) : PB :=
    @MkPB (λ Δ, ∃ (a : A), PBPB a Δ) _.
  Next Obligation.
    intros A PBPB Δ Δ' HΔ. by setoid_rewrite HΔ.
  Qed.

  Local Infix "⊢" := PB_entails.
  Local Notation "'emp'" := PB_emp.
  Local Infix "∗" := PB_sep.
  Local Infix "-∗" := PB_wand.
  Local Infix "∧" := PB_and.

  Lemma sep_mono P P' Q Q' :
    (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'.
  Proof.
    intros H1 H2 Δ.
    destruct 1 as (Δ1 & Δ2 & HΔ1 & HΔ2 & H3).
    do 2 eexists. repeat split; eauto.
  Qed.
  Lemma emp_sep_1 P : P ⊢ emp ∗ P.
  Proof.
    intros Δ HP. compute.
    eexists empty%B,_. repeat split.
    - done.
    - eapply HP.
    - by rewrite left_id.
  Qed.
  Lemma emp_sep_2 P : emp ∗ P ⊢ P.
  Proof.
    intros Δ HP. compute in HP.
    destruct HP as (Δ1 & Δ2 & H1 & H2 & ->).
    rewrite H1. by rewrite left_id.
  Qed.
  Lemma sep_comm' P Q : P ∗ Q ⊢ Q ∗ P.
  Proof.
    intros Δ (Δ1 & Δ2 & H1 & H2 & ->).
    rewrite (comm _ Δ1 Δ2).
    do 2 eexists. repeat split; eauto.
  Qed.
  Lemma sep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
  Proof.
    intros Δ (Δ1' & Δ3 & (Δ1 & Δ2 & H1 & H2 & H4) & H3 & ->).
    rewrite H4. rewrite -(assoc _ Δ1 Δ2 Δ3).
    do 2 eexists. repeat split; eauto.
    do 2 eexists. repeat split; eauto.
  Qed.
  Lemma wand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R.
  Proof.
    intros HH Δ HP.
    intros Δ' HQ. eapply HH.
    do 2 eexists. repeat split; eauto.
  Qed.
  Lemma wand_elim_l' P Q R : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R.
  Proof.
    intros HH Δ (Δ1 & Δ2 & H1 & H2 & ->).
    by eapply HH.
  Qed.

  Global Instance entails_preorder : PreOrder PB_entails.
  Proof. split; compute; naive_solver. Qed.

  Lemma PB_bi_mixin : BiMixin (PROP:=PB)
                              PB_entails PB_emp PB_pure PB_and PB_or
                              PB_impl PB_forall PB_exists PB_sep PB_wand.
  Proof.
    split; try by (compute; naive_solver).
    - apply _.
    - apply _.
    - apply emp_sep_1.
    - apply emp_sep_2.
    - apply sep_comm'.
    - apply sep_assoc'.
    - apply wand_elim_l'.
    (* - apply box_sep_elim. *)
  Qed.


  Canonical Structure PB_alg : bi :=
    {| bi_bi_mixin := PB_bi_mixin; |}.

End PB.

Module Cl.
  Import PB.

  Program Definition Fint (ϕ : formula) : PB :=
    {| PBPred := (λ Δ, Δ ⊢ᴮ ϕ) |}.
  Next Obligation. solve_proper. Qed.

  Definition ClBase := { X : PB | ∃ ϕ, X ≡ Fint ϕ }.

  Program Definition cl (X : PB) : PB :=
    @MkPB (λ Δ, ∀ (ϕ : formula), ((X : PB_alg) ⊢ Fint ϕ) → Δ ⊢ᴮ ϕ) _.
  Next Obligation.
    intros X Δ1 Δ2 HD. by setoid_rewrite HD.
  Qed.

  Lemma cl_unit X : X ⊢ cl (X : PB_alg).
  Proof.
    intros Δ Hx. simpl. intros ϕ Hϕ.
    by apply Hϕ.
  Qed.

  Lemma cl_mono (X Y : PB) : (X ⊢@{PB_alg} Y) → (cl X ⊢@{PB_alg} cl Y).
  Proof.
    intros HX Δ. simpl. intros H1 ϕ HY.
    eapply H1. by rewrite HX.
  Qed.

  Lemma cl_idemp (X : PB) : cl (cl X) ≡ cl X.
  Proof.
    split; last first.
    { eapply cl_unit. }
    simpl. intros H1 ϕ HX.
    eapply H1. intros Δ'. simpl.
    intros H2. by eapply H2.
  Qed.

  Lemma cl_alt_eq (X : PB) :
    (cl X : PB) ≡
      (∀ Z : { ϕ : formula | X ⊢@{PB_alg} Fint ϕ },
          Fint (proj1_sig Z) : PB_alg)%I.
  Proof.
    split.
    - simpl. intros H1.
      rewrite /bi_forall/PB_forall /=.
      intros [ϕ Hϕ]. simpl. by eapply H1.
    - simpl. intros H1 ϕ HX.
      apply (H1 (ϕ ↾ HX)).
  Qed.

  Global Instance cl_proper : Proper ((≡) ==> (≡)) cl.
  Proof.
    intros X Y HXY.
    split; eapply cl_mono; by rewrite HXY.
  Qed.

  Class Is_closed (X : PB) := closed_eq_cl : X ≡ cl X.

  Global Instance Is_closed_proper : Proper ((≡) ==> (↔)) Is_closed.
  Proof.
    intros X Y HXY. unfold Is_closed.
    by rewrite HXY.
  Qed.

  Lemma Is_closed_inc (X : PB) :
    ((cl X : PB_alg) ⊢ X) → Is_closed X.
  Proof.
    intros H1. unfold Is_closed.
    split.
    - eapply cl_unit.
    - eapply H1.
  Qed.

  Record C :=
    { CPred :> PB ; CPred_closed : Is_closed CPred }.
  Global Existing Instance CPred_closed.
  Global Instance CPred_proper (X : C) : Proper ((≡) ==> (↔)) X.
  Proof.
    intros D1 D2 HD.
    by apply PBPred_proper.
  Qed.

  Lemma C_intro (X : C) Δ :
    (∀ ϕ, (X ⊢@{PB_alg} Fint ϕ) → Δ ⊢ᴮ ϕ) →
    X Δ.
  Proof.
    destruct X as [X Xcl]. simpl.
    intros H1. rewrite Xcl. done.
  Qed.

  Program Definition Fint' ϕ : C :=
    {| CPred := Fint ϕ |}.
  Next Obligation.
    intros ϕ. apply Is_closed_inc.
    intros Δ Hcl. simpl. eapply Hcl.
    eauto.
  Qed.

  Lemma cl_alt_eq_2 (X : PB) :
    (cl X : PB) ≡
      (∀ Z : { Y : C | X ⊢@{PB_alg} Y }, `Z : PB_alg)%I.
  Proof.
    split.
    - simpl. intros H1.
      rewrite /bi_forall/PB_forall /=.
      intros [[Y HY] HXY]. simpl.
      rewrite HY. intros ϕ Hϕ.
      eapply H1. rewrite -Hϕ. eapply HXY.
    - simpl. intros H1 ϕ HX.
      apply (H1 (Fint' ϕ ↾ HX)).
  Qed.

  Lemma cl_alt_eq_3 (X : PB) :
    (cl X : PB) ≡
      (∀ Y : C, (⌜X ⊢@{PB_alg} Y⌝) → Y : PB_alg)%I.
  Proof.
    rewrite cl_alt_eq_2.
    split.
    - intros H1. rewrite /bi_forall /bi_impl /=.
      intros Y HXY. simpl.
      apply (H1 (Y ↾ HXY)).
    - intros H1. rewrite /bi_forall /bi_impl /=.
      intros [Y HXY]. simpl. apply H1.
      apply HXY.
  Qed.

  Lemma C_necessitate (X : C) Δ :
    X Δ → X (bunch_map BOX Δ).
  Proof.
    destruct X as [X Xcl]. simpl.
    intros HX. rewrite Xcl.
    intros ϕ Hϕ. eapply (BI_Boxes_L []).
    by apply Hϕ.
  Qed.

  Lemma C_bunch_box_idemp (X : C) Δ :
    X (bunch_map BOX (bunch_map BOX Δ)) → X (bunch_map BOX Δ).
  Proof.
    destruct X as [X Xcl]. simpl.
    intros HX. rewrite Xcl.
    intros ϕ Hϕ. eapply (box_l_inv []).
    by apply Hϕ.
  Qed.

  Lemma C_weaken (X : C) Δ Δ' :
    X Δ → X (Δ ;, Δ')%B.
  Proof.
    destruct X as [X Xcl]. simpl.
    intros HX. rewrite Xcl.
    intros ϕ Hϕ.
    eapply (BI_Weaken []). simpl.
    by apply Hϕ.
  Qed.

  Lemma C_contract (X : C) Δ :
    X (Δ ;, Δ)%B → X Δ.
  Proof.
    destruct X as [X Xcl]. simpl.
    intros HX. rewrite Xcl.
    intros ϕ Hϕ.
    eapply (BI_Contr []). simpl.
    by apply Hϕ.
  Qed.

  Lemma C_collapse (X : C) Γ Δ :
    X (fill Γ Δ) → X (fill Γ (frml (collapse Δ))).
  Proof.
    destruct X as [X Xcl]. simpl.
    revert Γ. induction Δ=>Γ; simpl; eauto.
    - intros HX. rewrite Xcl=>ϕ Hϕ.
      by apply BI_True_L, Hϕ.
    - intros HX. rewrite Xcl=>ϕ Hϕ.
      by apply BI_Emp_L, Hϕ.
    - intros HX. rewrite Xcl=>ϕ Hϕ.
      apply BI_Sep_L, Hϕ.
      apply (IHΔ1 (CtxCommaL _::Γ)); simpl.
      apply (IHΔ2 (CtxCommaR _::Γ)); simpl.
      apply HX.
    - intros HX. rewrite Xcl=>ϕ Hϕ.
      apply BI_Conj_L, Hϕ.
      apply (IHΔ1 (CtxSemicL _::Γ)); simpl.
      apply (IHΔ2 (CtxSemicR _::Γ)); simpl.
      apply HX.
  Qed.

  Lemma C_collapse_inv (X : C) Γ Δ :
    X (fill Γ (frml (collapse Δ))) → X (fill Γ Δ).
  Proof.
    destruct X as [X Xcl]. simpl.
    rewrite !Xcl. intros HX ϕ Hϕ.
    simpl in HX. apply collapse_l_inv.
    by apply HX.
  Qed.

  Program Definition cl' (X : PB) : C :=
    {| CPred := cl X |}.
  Next Obligation.
    intros X. unfold Is_closed. by rewrite cl_idemp.
  Qed.

  Global Instance C_equiv : Equiv C := PB_equiv.
  Global Instance C_equiv_equivalence : Equivalence (≡@{C}).
  Proof.
    rewrite /equiv /C_equiv /PB_equiv.
    split; repeat intro; naive_solver.
  Qed.

  Definition C_entails (X Y : C) : Prop := PB.PB_entails X Y.

  Global Instance C_entail_proper : Proper ((≡) ==> (≡) ==> (↔)) C_entails.
  Proof.
    intros X1 X2 HX Y1 Y2 HY. unfold C_entails.
    split.
    - intros H1 Δ.
      specialize (HX Δ).
      specialize (HY Δ).
      naive_solver.
    - intros H1 Δ.
      specialize (HX Δ).
      specialize (HY Δ).
      naive_solver.
  Qed.

  Program Definition C_and (X Y : C) : C :=
    {| CPred := ((X : PB_alg) ∧ Y)%I |}.
  Next Obligation.
    intros [X HX] [Y HY]. apply Is_closed_inc.
    rewrite /bi_and /=.
    intros Δ HΔ. split.
    + rewrite HX. intros ψ H'. eapply HΔ.
      rewrite -H'. intros ?. simpl. naive_solver.
    + rewrite HY. intros ψ H'. eapply HΔ.
      rewrite -H'. intros ?. simpl. naive_solver.
  Qed.

  Program Definition C_forall (A : Type) (CC : A → C) : C :=
    {| CPred := PB_forall A CC |}.
  Next Obligation.
    intros A CC.
    apply Is_closed_inc.
    eapply bi.forall_intro=>a.
    rewrite cl_alt_eq_3.
    rewrite (bi.forall_elim (CC a)).
    intros Δ H1. apply H1.
    rewrite /bi_pure /=.
    clear. by rewrite (bi.forall_elim a).
  Qed.

  Program Definition PB_impl' (X Y : PB) : PB :=
    @MkPB (λ Δ, ∀ Δ', X Δ' → Y (Δ ;, Δ')%B) _.
  Next Obligation.
    intros X Y D1 D2 H1. by setoid_rewrite H1.
  Qed.

  Program Definition C_impl (X : PB) (Y : C) : C :=
    {| CPred := PB_impl' X Y |}.
  Next Obligation.
    intros X Y.
    cut (PB_impl' X Y ≡
            @C_forall ({ Δ | X Δ } * { ϕ : formula | Y ⊢@{PB_alg} Fint ϕ })
            (λ '(Δ, ϕ), Fint' (IMPL (collapse (`Δ)) (`ϕ)))).
    { intros ->. by apply CPred_closed. }
    intro Δ. simpl. split.
    - intros HXY. intros ([Δ' HX], [ϕ Hϕ]).
      simpl. apply BI_Impl_R.
      apply Hϕ.
      apply (C_collapse _ [CtxSemicR Δ]).
      simpl. by apply HXY.
    - intros H Δ' HX.
      destruct Y as [Y Yc]. simpl.
      rewrite Yc. intros ψ Hψ.
      specialize (H ((Δ' ↾ HX), (ψ ↾ Hψ))). simpl in *.
      apply impl_r_inv in H.
      by apply (collapse_l_inv [CtxSemicR Δ]).
  Qed.

  Definition C_emp : C := cl' PB_emp.

  Program Definition C_sep (X Y : C) : C := cl' (PB_sep X Y).

  Program Definition C_or (X Y : C) : C := cl' (PB_or X Y).

  Program Definition C_exists (A : Type) (CC : A → C) : C :=
    cl' (PB_exists A CC).

  Program Definition C_wand (X : PB) (Y : C) : C :=
    {| CPred := PB_wand X Y |}.
  Next Obligation.
    intros X Y.
    cut (PB_wand X Y ≡
            @C_forall ({ Δ | X Δ } * { ϕ : formula | Y ⊢@{PB_alg} Fint ϕ })
            (λ '(Δ, ϕ), Fint' (WAND (collapse (`Δ)) (`ϕ)))).
    { intros ->. by apply CPred_closed. }
    intro Δ. simpl. split.
    - intros HXY. intros ([Δ' HX], [ϕ Hϕ]).
      simpl. apply BI_Wand_R.
      apply Hϕ.
      apply (C_collapse _ [CtxCommaR Δ]).
      simpl. by apply HXY.
    - intros H Δ' HX.
      destruct Y as [Y Yc]. simpl.
      rewrite Yc. intros ψ Hψ.
      specialize (H ((Δ' ↾ HX), (ψ ↾ Hψ))). simpl in *.
      apply wand_r_inv in H.
      by apply (collapse_l_inv [CtxCommaR Δ]).
  Qed.

  Program Definition PB_box (X: PB) : PB :=
    {| PBPred := λ Δ, ∃ Δ', Δ ≡ bunch_map BOX Δ' ∧ X Δ' |}.
  Next Obligation. solve_proper. Qed.
  Definition C_box (X : C) : C := cl' (PB_box X).

  Local Infix "⊢" := C_entails.
  Local Notation "'emp'" := C_emp.
  Local Infix "∗" := C_sep.
  Local Infix "-∗" := C_wand.
  Local Infix "→" := C_impl.
  Local Infix "∧" := C_and.
  Local Infix "∨" := C_or.
  Implicit Types P Q R : C.

  Lemma cl_adj (X : PB) (Y : C) :
    (X ⊢@{PB_alg} (Y : PB_alg)) → cl' X ⊢@{PB_alg} Y.
  Proof.
    intros H1 Δ.
    destruct Y as [Y Ycl].
    rewrite Ycl. eapply cl_mono.
    eapply H1.
  Qed.
  Lemma cl'_adj (X : PB) (Y : C) :
    (X ⊢@{PB_alg} (Y : PB_alg)) → cl' X ⊢ Y.
  Proof.
    intros H1 Δ.
    destruct Y as [Y Ycl].
    rewrite Ycl. eapply cl_mono.
    eapply H1.
  Qed.

  Lemma impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R.
  Proof.
    intros H1 Δ HP. intros Δ' HQ.
    apply H1. split.
    - by apply C_weaken.
    - rewrite comm. by apply C_weaken.
  Qed.
  Lemma impl_elim_l' (P Q R : C) : (P ⊢ Q → R) → P ∧ Q ⊢ R.
  Proof.
    intros H1 Δ [HP1 HP2]. apply C_contract.
    by apply H1.
  Qed.
  Lemma or_intro_l (P Q : C) : P ⊢ P ∨ Q.
  Proof.
    intros Δ HP. eapply cl_unit. naive_solver.
  Qed.
  Lemma or_intro_r (P Q : C) : Q ⊢ P ∨ Q.
  Proof.
    intros Δ HP. eapply cl_unit. naive_solver.
  Qed.

  Lemma sep_mono P P' Q Q' :
    (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'.
  Proof.
    intros H1 H2 Δ HP ϕ Hϕ.
    apply (HP ϕ). clear HP Δ.
    intros Δ. destruct 1 as (Δ1 & Δ2 & HΔ1 & HΔ2 & ->).
    eapply Hϕ. do 2 eexists. split; eauto.
  Qed.

  Lemma wand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R.
  Proof.
    intros HH Δ HP.
    intros Δ' HQ. eapply HH.
    eapply cl_unit.
    do 2 eexists. repeat split; eauto.
  Qed.
  Lemma wand_elim_l' (P Q R : C) : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R.
  Proof.
    destruct R as [R HR].
    intros HH Δ HPQ. simpl.
    rewrite HR. intros ϕ Hϕ. eapply HPQ.
    clear Δ HPQ. intros Δ (Δ1 & Δ2 & H1 & H2 & ->).
    apply Hϕ. by apply HH.
  Qed.

  Lemma emp_sep_1 P : P ⊢ emp ∗ P.
  Proof.
    intros Δ HP. eapply cl_unit.
    exists empty, Δ. rewrite left_id.
    repeat split; eauto.
    intros ϕ Hϕ. eapply Hϕ. simpl. reflexivity.
  Qed.
  Lemma emp_sep_2 P : emp ∗ P ⊢ P.
  Proof.
    apply wand_elim_l'.
    eapply cl'_adj. eapply PB.wand_intro_r.
    rewrite PB.emp_sep_2. done.
  Qed.
  Lemma sep_comm' P Q : P ∗ Q ⊢ Q ∗ P.
  Proof. apply cl_mono. apply sep_comm'. Qed.
  Lemma sep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
  Proof.
    apply wand_elim_l'.
    apply cl'_adj.
    intros Δ (D1 & D2 & HD1 & HD2 & ->).
    intros D3 HD3. apply cl_unit.
    exists D1, (D2 ,, D3)%B.
    rewrite (assoc _ D1). repeat split; eauto.
    apply cl_unit. do 2 eexists; repeat split; eauto.
  Qed.

  Global Instance c_entails_preorder : PreOrder C_entails.
  Proof. split; compute; naive_solver. Qed.

  Definition C_pure (ϕ : Prop) : C := cl' (PB_pure ϕ).

  Program Definition PB_top : PB :=
    {| PBPred := (λ Δ, Δ ≡ top) |}.

  Next Obligation. solve_proper. Qed.

  Definition C_top := cl' PB_top.

  Lemma C_true_top : C_pure True ⊢ C_top.
  Proof.
    apply cl_adj.
    intros Δ _.
    rewrite -(BE_semic_unit_l Δ).
    apply C_weaken. apply cl_unit.
    simpl. reflexivity.
  Qed.
  Lemma C_top_true : C_top ⊢ C_pure True.
  Proof. intros Δ _. apply cl_unit. done. Qed.

  Lemma box_mono P Q : (P ⊢ Q) → C_box P ⊢ C_box Q.
  Proof.
    intros HH. apply cl_mono.
    intros Δ. simpl. destruct 1 as (Δ' & HD & HP).
    exists Δ'. split; auto.
  Qed.
  Lemma box_elim P : C_box P ⊢ P.
  Proof.
    apply cl_adj. intros Δ. simpl.
    destruct 1 as (Δ' & HD & HP). rewrite HD.
    by apply C_necessitate.
  Qed.
  Lemma box_idem P : C_box P ⊢ C_box (C_box P).
  Proof.
    apply cl_adj. intros Δ.
    destruct 1 as (Δ' & HD & HP).
    rewrite HD.
    apply C_bunch_box_idemp. apply cl_unit.
    eexists. split; eauto. apply cl_unit.
    eexists. eauto.
  Qed.

  Lemma box_conj X Y : C_box X ∧ C_box Y ⊢ C_box (X ∧ Y).
  Proof.
    apply impl_elim_l'. apply cl_adj.
    intros Δ.
    destruct 1 as (Δ' & HD & HX).
    simpl. intros D1 H1 f Hf. rewrite HD.
    rewrite comm. apply (collapse_l_inv [CtxSemicR D1]). simpl.
    apply impl_r_inv. apply H1.
    intros D2. destruct 1 as (D2' & HD2 & HY). simpl.
    apply BI_Impl_R.
    apply (C_collapse (Fint' f) [CtxSemicR D2]). simpl.
    rewrite HD2.
    apply Hf. exists (D2';,Δ')%B. split.
    { simpl. done. }
    split.
    - rewrite comm. by apply C_weaken.
    - by apply C_weaken.
  Qed.

  Lemma box_sep X Y : C_box X ∗ C_box Y ⊢ C_box (X ∗ Y).
  Proof.
    apply wand_elim_l'. apply cl'_adj.
    apply bi.wand_intro_r.
    rewrite bi.sep_comm.
    apply bi.wand_elim_l'.
    change (C_box Y ⊢ PB_box X -∗ C_box (C_sep X Y)).
    apply cl_adj. apply bi.wand_intro_r.
    intros ? (Δ1 & Δ2 & (Θ1 & HT1 & HX) & (Θ2 & HT2 & HY) & ->).
    rewrite HT1 HT2. apply cl_unit.
    exists (Θ1,, Θ2)%B. split; auto.
    apply cl_unit.
    do 2 eexists; repeat split; eauto.
    by rewrite comm.
  Qed.

  Lemma box_true : C_pure True ⊢ C_box (C_pure True).
  Proof.
    apply cl_adj. intros Δ _.
    rewrite -(BE_semic_unit_l Δ).
    apply C_weaken. apply cl_unit.
    simpl. exists top. simpl. split; auto.
    apply cl_unit. done.
  Qed.

  Lemma box_emp : emp ⊢ C_box emp.
  Proof.
    apply cl_mono. intros Δ HD; simpl.
    exists empty. split; eauto. apply cl_unit.
    simpl. reflexivity.
  Qed.

  (* not needed? *)
  Lemma box_conj_2 X Y : C_box (X ∧ Y) ⊢ C_box X ∧ C_box Y.
  Proof.
    apply cl_adj. intros Δ; simpl.
    destruct 1 as (Δ' & -> & HΔ').
    destruct HΔ' as (H1 & H2). split.
    - apply cl_unit. exists Δ'. split; eauto.
    - apply cl_unit. exists Δ'. split; eauto.
  Qed.

  Lemma C_bi_mixin : BiMixin (PROP:=C)
                              C_entails C_emp C_pure C_and C_or
                              C_impl C_forall C_exists C_sep C_wand.
  Proof.
    split.
    - apply _.
    - apply _.
    - intros ??. split.
      { by intros ->. }
      intros [H1 H2]. split.
      + apply H1.
      + apply H2.
    - intros n A1 A2 HA. compute.
      naive_solver.
    - intros [X1 ?] [X2 ?] HX [Y1 ?] [Y2 ?] HY.
      intros Δ.
      specialize (HX Δ).
      specialize (HY Δ).
      simpl in *. compute; naive_solver.
    - intros X1 X2 HX Y1 Y2 HY; try apply _.
      apply cl_proper. intros Δ.
      specialize (HX Δ).
      specialize (HY Δ).
      compute; naive_solver.
    - intros X1 X2 HX Y1 Y2 HY; try apply _.
      intros Δ.
      split.
      + intros HX1 Δ2 HD2.
        apply HY, HX1.
        by apply HX.
      + intros HX1 Δ2 HD2.
        apply HY, HX1.
        by apply HX.
    - intros A P1 P2 HP.
      intros Δ. split.
      + intros H1 x. apply HP, H1.
      + intros H2 x. apply HP, H2.
    - intros A P1 P2 HP.
      apply cl_proper.
      intros Δ. split.
      + intros [x H1]. exists x. by apply HP.
      + intros [x H2]. exists x. by apply HP.
    - intros X1 X2 HX Y1 Y2 HY; try apply _.
      apply cl_proper.
      intros Δ. split.
      + intros (D1 & D2 & H1 & H2 & ->).
        do 2 eexists. repeat split; eauto.
        * by apply HX.
        * by apply HY.
      + intros (D1 & D2 & H1 & H2 & ->).
        do 2 eexists. repeat split; eauto.
        * by apply HX.
        * by apply HY.
    - intros X1 X2 HX Y1 Y2 HY; try apply _.
      intros Δ. split.
      + intros HX1 Δ2 HD2.
        apply HY, HX1.
        by apply HX.
      + intros HX1 Δ2 HD2.
        apply HY, HX1.
        by apply HX.
    - intros ψ X Hψ Δ. simpl.
      intros HX ϕ Hs. apply Hs.
      done.
    - intros ψ X Hψ.
      apply cl'_adj.
      intros Δ HHψ. apply Hψ; eauto.
      simpl. intros ϕ Hϕ. apply Hϕ.
      done.
    - compute; intros; naive_solver.
    - compute; intros; naive_solver.
    - compute; intros; naive_solver.
    - compute; intros; naive_solver.
    - compute; intros; naive_solver.
    - intros P Q R H1 H2.
      apply cl'_adj=>Δ [H|H]; eauto.
    - apply impl_intro_r.
    - apply impl_elim_l'.
    - intros A X P HP.
      intros Δ HD a. by apply HP.
    - intros A X P Δ HP. apply HP.
    - intros A X a Δ HP.
      apply cl_unit. exists a. eauto.
    - intros A P X HP. apply cl'_adj.
      intros Δ [a Ha]. by apply (HP a).
    - apply sep_mono.
    - apply emp_sep_1.
    - apply emp_sep_2.
    - apply sep_comm'.
    - apply sep_assoc'.
    - apply wand_intro_r.
    - apply wand_elim_l'.
  Qed.

Canonical Structure C_alg : bi :=
  {| bi_bi_mixin := C_bi_mixin; |}.

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

Definition C_atom (a : atom) := Fint' (ATOM a).

Definition inner_interp : formula → C
  := formula_interp C_alg C_box C_atom.

Lemma okada_property (A : formula) :
  ((inner_interp A) (frml A)) ∧ (inner_interp A ⊢@{C_alg} Fint' A).
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
      * eapply Hϕ. apply cl_unit.
        by left.
      * eapply Hϕ. apply cl_unit.
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
      apply cl_unit. exists (frml A1), (frml A2).
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
      { by apply IH12. }
      simpl. by apply Hϕ.
    + intros Δ H1. simpl.
      constructor. apply IH22.
      by apply H1.
  - destruct IHA1 as [IH11 IH12].
    destruct IHA2 as [IH21 IH22].
    split.
    + move=> Δ' HΔ'.
      apply C_intro=>ϕ Hϕ.
      rewrite comm.
      apply (BI_Wand_L []).
      { by apply IH12. }
      simpl. by apply Hϕ.
    + intros Δ H1. simpl.
      constructor. apply IH22.
      by apply H1.
  - destruct IHA as [IH1 IH2].
    split.
    + intros ϕ Hϕ. apply Hϕ. simpl.
      exists (frml A). split; eauto.
    + apply cl_adj. intros ? (Δ & -> & HA).
      simpl. apply BI_Box_R. apply IH2.
      by apply C_necessitate.
Qed.

End Cl.

Import PB Cl.

Theorem cut Γ Δ ϕ ψ :
  (Δ ⊢ᴮ ψ) →
  (fill Γ (frml ψ) ⊢ᴮ ϕ) →
  fill Γ Δ ⊢ᴮ ϕ.
Proof.
  intros H1%(seq_interp_sound C_alg C_box C_atom).
  intros H2%(seq_interp_sound C_alg C_box C_atom).
  simpl in H1, H2.
  cut (seq_interp C_alg C_box C_atom (fill Γ Δ) ϕ).
  { simpl. intros H3.
    destruct (okada_property ϕ) as [Hϕ1 Hϕ2].
    apply Hϕ2. unfold inner_interp.
    apply H3. apply (C_collapse_inv _ [] (fill Γ Δ)). simpl.
    cut (formula_interp C_alg C_box C_atom (collapse (fill Γ Δ)) (frml (collapse (fill Γ Δ)))).
    { apply (bunch_interp_collapse C_alg C_box C_atom). }
    apply okada_property. }
  simpl. rewrite -H2.
  apply bunch_interp_fill_mono, H1.
Qed.

(* Print Assumptions cut. *)
(*  ==> Closed under the global context *)
