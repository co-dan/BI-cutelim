(* Semantic proof of cut elimination.. *)
From Coq Require Import ssreflect.
From stdpp Require Import prelude gmap.
From bunched.algebra Require Import bi.
From Equations Require Import Equations.
From bunched Require Import seqcalc seqcalc_height interp terms syntax.

(** * Parameters to the proof: a list of simple structural extensions *)
Parameter rules : list (list (bterm nat) * bterm nat).
Parameter rules_good : forall (Ts : list (bterm nat)) (T : bterm nat),
    (Ts, T) ∈ rules → linear_bterm T.

Module M.
  Definition rules := rules.
  Definition rules_good := rules_good.
End M.
Module SH := SeqcalcHeight(M).
Module S := Seqcalc(M).
Import SH S.

(** * Construction of the powerset algebra over the monoid of bunches *)
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

  Global Instance PB_and_proper : Proper ((≡) ==> (≡) ==> (≡)) PB_and.
  Proof. compute; naive_solver. Qed.

  Program Definition PB_impl (X Y : PB) : PB :=
    {| PBPred := (λ Δ, X Δ → Y Δ) |}.
  Next Obligation.
    intros X Y Δ Δ' HΔ. rewrite HΔ.
    eauto.
  Qed.

  Global Instance PB_impl_proper : Proper ((≡) ==> (≡) ==> (≡)) PB_impl.
  Proof. compute; naive_solver. Qed.

  Program Definition PB_emp : PB :=
    {| PBPred := (λ Δ, Δ ≡ empty) |}.
  Next Obligation. solve_proper. Qed.

  Program Definition PB_sep (X Y : PB) : PB :=
    {| PBPred := (λ Δ, ∃ Δ1 Δ2, X Δ1 ∧ Y Δ2 ∧ (Δ ≡ (Δ1 ,, Δ2)%B)) |}.
  Next Obligation. solve_proper. Qed.

  Global Instance PB_sep_proper : Proper ((≡) ==> (≡) ==> (≡)) PB_sep.
  Proof. compute; naive_solver. Qed.

  Program Definition PB_wand (X Y : PB) : PB :=
    @MkPB (λ Δ, ∀ Δ1, X Δ1 → Y (Δ ,, Δ1)%B) _.
  Next Obligation.
    intros X Y Δ Δ' HΔ. by setoid_rewrite HΔ.
  Qed.

  Global Instance PB_wand_proper : Proper ((≡) ==> (≡) ==> (≡)) PB_wand.
  Proof. compute; naive_solver. Qed.

  Definition PB_pure (ϕ : Prop) : PB := MkPB (λ _, ϕ).

  Program Definition PB_or (X Y : PB) : PB :=
    {| PBPred := (λ Δ, X Δ ∨ Y Δ)%B |}.
  Next Obligation. solve_proper. Qed.

  Global Instance PB_or_proper : Proper ((≡) ==> (≡) ==> (≡)) PB_or.
  Proof. compute; naive_solver. Qed.

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
  Qed.


  Canonical Structure PB_alg : bi :=
    {| bi_bi_mixin := PB_bi_mixin; |}.

End PB.

(** * Construction of the algebra of closed sets *)
Module Cl.
  Import PB.

  (* Definition of the principal closed sets and the closure operator *)
  Program Definition Fint (ϕ : formula) : PB :=
    {| PBPred := (λ Δ, Δ ⊢ᴮ ϕ) |}.
  Next Obligation. solve_proper. Qed.

  Program Definition cl (X : PB) : PB :=
    @MkPB (λ Δ, ∀ (ϕ : formula), ((X : PB_alg) ⊢ Fint ϕ) → Δ ⊢ᴮ ϕ) _.
  Next Obligation.
    intros X Δ1 Δ2 HD. by setoid_rewrite HD.
  Qed.

  Class Is_closed (X : PB) := closed_eq_cl : X ≡ cl X.

  Record C :=
    { CPred :> PB ; CPred_closed : Is_closed CPred }.

  Global Instance C_equiv : Equiv C := PB_equiv.
  Definition C_entails (X Y : C) : Prop := PB_entails X Y.

  (* Instances and laws needed to define other connectives *)
  Global Instance ElemOf_PB : ElemOf bunch PB := λ a X, X a.
  Global Instance ElemOf_C : ElemOf bunch C := λ a X, X a.

  Global Existing Instance CPred_closed.

  Global Instance CPred_proper (X : C) : Proper ((≡) ==> (↔)) X.
  Proof.
    intros D1 D2 HD.
    by apply PBPred_proper.
  Qed.

  Global Instance C_equiv_equivalence : Equivalence (≡@{C}).
  Proof.
    rewrite /equiv /C_equiv /PB_equiv.
    split; repeat intro; naive_solver.
  Qed.

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

  (* monadic operations for cl *)
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

  Lemma cl_adj (X : PB) (Y : PB) `{!Is_closed Y} :
    (X ⊢@{PB_alg} Y) → cl X ⊢@{PB_alg} Y.
  Proof.
    rewrite (@closed_eq_cl Y).
    rewrite -{2}(cl_idemp Y).
    apply cl_mono.
  Qed.

  Global Instance cl_proper : Proper ((≡) ==> (≡)) cl.
  Proof.
    intros X Y HXY.
    split; eapply cl_mono; by rewrite HXY.
  Qed.

  Global Instance Is_closed_cl (X : PB) : Is_closed (cl X).
  Proof.
    rewrite /Is_closed. by rewrite cl_idemp.
  Qed.

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

  (* Specializing [cl : PB → PB] to [PB → C] *)
  Program Definition cl' (X : PB) : C :=
    {| CPred := cl X |}.

  Program Definition Fint' ϕ : C :=
    {| CPred := Fint ϕ |}.
  Next Obligation.
    intros ϕ. apply Is_closed_inc.
    intros Δ Hcl. simpl. eapply Hcl.
    eauto.
  Qed.

  (* Alternative descriptions of the closure operator, internally in
  the language of the BI algebra *)
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

  (* General closure properties of closed sets *)
  Lemma C_inhabited (X : C) : X (frml BOT).
  Proof.
    destruct X as [X Xcl]. simpl.
    rewrite Xcl. intros ϕ Hϕ.
    eapply (BI_False_L []).
  Qed.

  Lemma C_intro (X : C) Δ :
    (∀ ϕ, (X ⊢@{PB_alg} Fint ϕ) → Δ ⊢ᴮ ϕ) →
    X Δ.
  Proof.
    destruct X as [X Xcl]. simpl.
    intros H1. rewrite Xcl. done.
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
    rewrite !Xcl. intros HX ϕ Hϕ.
    simpl in HX. apply collapse_l.
    by apply HX.
  Qed.

  Lemma C_collapse_inv (X : C) Γ Δ :
    X (fill Γ (frml (collapse Δ))) → X (fill Γ Δ).
  Proof.
    destruct X as [X Xcl]. simpl.
    rewrite !Xcl. intros HX ϕ Hϕ.
    simpl in HX. apply collapse_l_inv.
    by apply HX.
  Qed.

  Global Instance PB_and_Is_closed X Y :
    Is_closed X →
    Is_closed Y →
    Is_closed (PB_and X Y).
  Proof.
    intros HX HY.
    apply Is_closed_inc.
    intros Δ HΔ. split.
    + rewrite HX. intros ψ H'. eapply HΔ.
      rewrite -H'. intros ?. simpl. naive_solver.
    + rewrite HY. intros ψ H'. eapply HΔ.
      rewrite -H'. intros ?. simpl. naive_solver.
  Qed.

  Program Definition C_and (X Y : C) : C :=
    {| CPred := ((X : PB_alg) ∧ Y)%I |}.

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

  Global Instance PB_impl'_proper : Proper ((≡) ==> (≡) ==> (≡)) PB_impl'.
  Proof. compute; naive_solver. Qed.

  Global Instance PB_wand_Is_closed (X : PB) (Y : PB) :
    Is_closed Y →
    Is_closed (PB_wand X Y).
  Proof.
    rewrite {1}/Is_closed. intros HYc. rewrite HYc.
    cut (PB_wand X (cl Y) ≡
            @C_forall ({ Δ | X Δ } * { ϕ : formula | (cl Y) ⊢@{PB_alg} Fint ϕ })
            (λ '(Δ, ϕ), Fint' (WAND (collapse (`Δ)) (`ϕ)))).
    { intros ->. by apply CPred_closed. }
    intro Δ. simpl. split.
    - intros HXY. intros ([Δ' HX], [ϕ Hϕ]).
      simpl. apply BI_Wand_R.
      apply Hϕ.
      apply (C_collapse (cl' Y) [CtxCommaR Δ]).
      simpl. by apply HXY.
    - intros H Δ' HX.
      intros ψ. rewrite HYc. intros Hψ.
      specialize (H ((Δ' ↾ HX), (ψ ↾ Hψ))). simpl in *.
      apply wand_r_inv in H.
      by apply (collapse_l_inv [CtxCommaR Δ]).
  Qed.

  Global Instance PB_impl_Is_closed (X : PB) (Y : PB) :
    Is_closed Y →
    Is_closed (PB_impl' X Y).
  Proof.
    rewrite {1}/Is_closed. intros HYc. rewrite HYc.
    cut (PB_impl' X (cl Y) ≡
            @C_forall ({ Δ | X Δ } * { ϕ : formula | (cl Y) ⊢@{PB_alg} Fint ϕ })
            (λ '(Δ, ϕ), Fint' (IMPL (collapse (`Δ)) (`ϕ)))).
    { intros ->. by apply CPred_closed. }
    intro Δ. simpl. split.
    - intros HXY. intros ([Δ' HX], [ϕ Hϕ]).
      simpl. apply BI_Impl_R.
      apply Hϕ.
      apply (C_collapse (cl' Y) [CtxSemicR Δ]).
      simpl. by apply HXY.
    - intros H Δ' HX.
      intros ψ. rewrite HYc. intros Hψ.
      specialize (H ((Δ' ↾ HX), (ψ ↾ Hψ))). simpl in *.
      apply impl_r_inv in H.
      by apply (collapse_l_inv [CtxSemicR Δ]).
  Qed.


  Program Definition C_impl (X : PB) (Y : C) : C :=
    {| CPred := PB_impl' X Y |}.

  Definition C_emp : C := cl' PB_emp.

  Program Definition C_sep (X Y : C) : C := cl' (PB_sep X Y).

  Program Definition C_or (X Y : C) : C := cl' (PB_or X Y).

  Program Definition C_exists (A : Type) (CC : A → C) : C :=
    cl' (PB_exists A CC).

  Program Definition C_wand (X Y : C) : C :=
    {| CPred := PB_wand X Y |}.

  Local Infix "⊢" := C_entails.
  Local Notation "'emp'" := C_emp.
  Local Infix "∗" := C_sep.
  Local Infix "-∗" := C_wand.
  Local Infix "→" := C_impl.
  Local Infix "∧" := C_and.
  Local Infix "∨" := C_or.

  Lemma cl'_adj (X : PB) (Y : C) :
    (X ⊢@{PB_alg} (Y : PB_alg)) → cl' X ⊢ Y.
  Proof.
    intros H1. apply cl_adj.
    { apply _. }
    apply H1.
  Qed.
  Lemma impl_intro_r (P Q R : C) : (P ∧ Q ⊢ R) → P ⊢ Q → R.
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
  Lemma wand_elim_l' P Q R : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R.
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

  Global Instance c_entails_preorder : PreOrder C_entails.
  Proof. split; compute; naive_solver. Qed.

  Definition C_pure (ϕ : Prop) : C := cl' (PB_pure ϕ).

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
    - intros A1 A2 HA. compute.
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

Definition C_later (X : C) : C := X.

Canonical Structure C_alg : bi :=
  {| bi_bi_mixin := C_bi_mixin; |}.

(** We now show that [cl] is an embedding from [C] to [PB] *)
Lemma cl_sep (X Y : PB) :
  cl' (PB_sep X Y) ≡ C_sep (cl' X) (cl' Y).
Proof.
  rewrite /C_sep.
  split.
  { apply cl_mono. f_equiv; apply cl_unit. }
  revert Δ.
  cut (cl' (PB_sep (cl' X) (cl' Y)) ⊢ cl' (PB_sep X Y)).
  { intros H1 Δ. apply (H1 Δ). }
  eapply cl'_adj.
  eapply bi.wand_elim_l'.
  apply (cl'_adj X (cl' Y -∗ cl' (PB_sep X Y))).
  apply bi.wand_intro_l.
  apply bi.wand_elim_l'.
  simpl.
  apply cl_adj.
  { apply _. }
  apply bi.wand_intro_l. apply cl_unit.
Qed.

Definition C_atom (a : atom) := Fint' (ATOM a).

Definition inner_interp : formula → C
  := formula_interp C_alg C_atom.


Lemma pas_de_deux (A : formula) :
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
Qed.

Lemma bterm_C_refl `{!EqDecision V, !Countable V}
      (T : bterm V) (Xs : V → C_alg) :
  ∀ (Δs : V → bunch),
    (forall (i : V), (Δs i) ∈ (Xs i)) ->
    bterm_ctx_act T Δs ∈ bterm_alg_act T Xs.
Proof.
  intros Δs HΔ.
  induction T; simpl.
  - apply HΔ.
  - apply cl_unit. do 2 eexists.
    repeat split; last reflexivity.
    + apply IHT1.    + apply IHT2.
  - split.
    + by apply C_weaken.
    + rewrite comm. by apply C_weaken.
Qed.

End Cl.

Import PB Cl.


(** ** An alternative description of the closed sets `T[Xs]` for linear terms *)

(* T[Xs] = { T[Δs] | ∀ i, Δs i ∈ Xs i } *)
Program Definition PB_blinterm_interp `{!EqDecision V, !Countable V} 
      (T : bterm V) (Xs : V → C_alg) : PB :=
  {| PBPred := λ Δ, ∃ (Δs : V → bunch),
    (forall (i : V), (Δs i) ∈ (Xs i)) ∧
    Δ ≡ bterm_ctx_act T Δs |}.
Next Obligation. solve_proper. Qed.

Definition C_blinterm_interp `{!EqDecision V, !Countable V}
   (T : bterm V) (Xs : V → C_alg) : C := cl' (PB_blinterm_interp T Xs).

Lemma blinterm_C_desc `{!EqDecision V, !Countable V}
      (T : bterm V) (TL : linear_bterm T)
      (Xs : V → C_alg) :
  bterm_alg_act (PROP:=C_alg) T Xs ⊢ C_blinterm_interp T Xs.
Proof.
  revert Xs. induction T=>Xs /=.
  - intros Δ HXs. apply cl_unit.
    exists (λ (i : V),
            match decide (i = x) with
            | left _ => Δ
            | right _ => frml BOT
            end).
    rewrite /= decide_True//.
    split; last done.
    intros i. case_decide; simplify_eq/=; auto.
    apply C_inhabited.
  - simp linear_bterm in TL.
    destruct TL as (Hfv & HL1 & HL2).
    rewrite IHT1 //. rewrite IHT2 //.
    apply cl_adj. { apply _. }
    apply bi.wand_elim_l'.
    apply cl_adj. { apply _. }
    apply bi.wand_intro_r.
    apply bi.wand_elim_r'.
    apply cl_adj. { apply _. }
    apply bi.wand_intro_l.
    intros Δ.
    intros (Δ1 & Δ2 & H1 & H2 & ->).
    destruct H1 as (Δs1 & HΔs1 & HDs1eq).
    destruct H2 as (Δs2 & HΔs2 & HDs2eq).
    apply cl_unit. simpl.
    pose (Δs := λ (x : V),
            match decide (x ∈ term_fv T1) with
            | left _ => Δs1 x
            | right _ => Δs2 x
            end).
    exists Δs. split.
    + intros i. unfold Δs.
      case_decide; auto.
    + assert (bterm_ctx_act T1 Δs1 = bterm_ctx_act T1 Δs) as <-.
      { apply bterm_ctx_act_fv.
        unfold Δs. intros i Hi.
        case_decide; auto. exfalso. auto. }
      assert (bterm_ctx_act T2 Δs2 = bterm_ctx_act T2 Δs) as <-.
      { apply bterm_ctx_act_fv.
        unfold Δs. intros i Hi.
        case_decide; auto. exfalso.
        revert Hfv Hi. set_unfold.
        naive_solver. }
      by f_equiv.
  - simp linear_bterm in TL.
    destruct TL as (Hfv & HL1 & HL2).
    rewrite IHT1 //. rewrite IHT2 //.
    intros Δ [H1 H2] ϕ Hϕ.
    eapply (BI_Contr []) ; simpl.
    simpl in *.
    apply (collapse_l_inv ([CtxSemicR Δ])).
    simpl. apply impl_r_inv.
    eapply H1.
    intros Δ1 HΔ1. simpl.
    apply BI_Impl_R.
    rewrite comm.
    apply (collapse_l [CtxSemicL Δ1]). simpl.
    apply (collapse_l_inv ([CtxSemicR Δ])). simpl.
    apply impl_r_inv.
    eapply H2.
    intros Δ2 HΔ2. simpl.
    apply BI_Impl_R. rewrite comm.
    apply (collapse_l [CtxSemicL Δ2]). simpl.
    eapply Hϕ.
    destruct HΔ1 as (Δs1 & HΔs1 & HDs1eq).
    destruct HΔ2 as (Δs2 & HΔs2 & HDs2eq).
    pose (Δs := λ (x : V),
            match decide (x ∈ term_fv T1) with
            | left _ => Δs1 x
            | right _ => Δs2 x
            end).
    exists Δs. split.
    + intros i. unfold Δs.
      case_decide; auto.
    + simpl.
      assert (bterm_ctx_act T1 Δs1 = bterm_ctx_act T1 Δs) as <-.
      { apply bterm_ctx_act_fv.
        unfold Δs. intros i Hi.
        case_decide; auto. exfalso. auto. }
      assert (bterm_ctx_act T2 Δs2 = bterm_ctx_act T2 Δs) as <-.
      { apply bterm_ctx_act_fv.
        unfold Δs. intros i Hi.
        case_decide; auto. exfalso.
        revert Hfv Hi. set_unfold.
        naive_solver. }
      by f_equiv.
Qed.

Lemma C_extensions (Ts : list (bterm nat)) (T : bterm nat) :
    (Ts, T) ∈ M.rules → rule_valid C_alg Ts T.
Proof.
  intros Hs. unfold rule_valid.
  intros Xs.
  trans (bterm_alg_act (PROP:=C_alg) T (cl' ∘ ( Xs))).
  { apply bterm_alg_act_mono.
    intros i. apply cl_unit. }
  assert (linear_bterm T) as Hlin.
  { eapply rules_good; eauto. }
  rewrite blinterm_C_desc //.
  apply cl_adj. { apply _. }
  rewrite /bi_exist /=.
  intros Δ H1 ϕ Hϕ ; auto.
  destruct H1 as (Δs & HΔs & H1).
  rewrite H1. eapply (BI_Simple_Ext []); eauto.
  intros Ti HTi. simpl. apply Hϕ.
  exists (Ti ↾ HTi). simpl. eapply bterm_C_refl.
  intros i. specialize (HΔs i). revert HΔs.
  simpl. generalize (Xs i)=>X. apply X.
Qed.

Theorem cut Γ Δ ϕ ψ :
  (Δ ⊢ᴮ ψ) →
  (fill Γ (frml ψ) ⊢ᴮ ϕ) →
  fill Γ Δ ⊢ᴮ ϕ.
Proof.
  intros H1%(seq_interp_sound (PROP:=C_alg) C_atom); last first.
  { apply C_extensions. }
  intros H2%(seq_interp_sound (PROP:=C_alg) C_atom); last first.
  { apply C_extensions. }
  simpl in H1, H2.
  cut (seq_interp C_alg C_atom (fill Γ Δ) ϕ).
  { simpl. intros H3.
    destruct (pas_de_deux ϕ) as [Hϕ1 Hϕ2].
    apply Hϕ2. unfold inner_interp.
    apply H3. apply (C_collapse_inv _ [] (fill Γ Δ)). simpl.
    cut (formula_interp C_alg C_atom (collapse (fill Γ Δ)) (frml (collapse (fill Γ Δ)))).
    { apply (bunch_interp_collapse C_alg C_atom). }
    apply pas_de_deux. }
  simpl. rewrite -H2.
  apply bunch_interp_fill_mono, H1.
Qed.

(* Print Assumptions cut. *)
(* ==> Depends only on rules and rules_good *)
