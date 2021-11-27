(* Semantic proof of cut elimination.. *)
From Coq Require Import ssreflect.
From stdpp Require Import prelude gmap.
From bunched.algebra Require Import bi from_monoid from_closure.
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

(** * Construction of the 'universal' cf-provability algebra *)
(** The first algebra that we consider is a purely "combinatorial" one:
    predicates [(bunch/≡) → Prop] *)

Global Instance bunch_monoid : Monoid comma :=
  {| monoid_unit := empty |}.

Definition PB := PB bunch.
Definition PB_alg := PB_alg bunch comma.

(** ** Principal closed sets *)
Program Definition Fint (ϕ : formula) : PB :=
  {| PBPred := (λ Δ, Δ ⊢ᴮ ϕ) |}.
Next Obligation. solve_proper. Qed.

Definition C := C bunch comma formula Fint.
Definition cl : PB → PB := cl bunch comma formula Fint.
Definition cl' : PB → C := cl' bunch comma formula Fint.

Definition CPred' : C → PB := CPred bunch comma formula Fint.
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
  apply collapse_l. by apply (Hϕ _).
Qed.

Lemma C_collapse_inv (X : C) Γ Δ :
  fill Γ (frml (collapse Δ)) ∈ X → fill Γ Δ ∈ X.
Proof.
  intros HX.
  apply C_intro=>ϕ Hϕ.
  apply collapse_l_inv. by apply (Hϕ _).
Qed.

(** Some calculations in the model. *)
Program Definition PB_and_alt (X Y : PB) :=
  MkPB bunch (λ Δ, ∃ Δ1 Δ2, (Δ ≡ (Δ1;,Δ2)%B) ∧
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
  MkPB bunch (λ Δ, ∀ Δ', Δ' ∈ X → (Δ ;, Δ')%B ∈ Y) _.
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
  change (from_closure.cl bunch comma formula Fint) with cl.
  change (cl (X -∗ (Y : PB)) ⊢@{PB_alg} X -∗ (Y : PB)).
  cut (PB_forall _ ({ Δ | X Δ } * { ϕ : formula | (Y : PB) ⊢@{PB_alg} Fint ϕ })
               (λ '(Δ, ϕ), Fint' (WAND (collapse (`Δ)) (`ϕ)) : PB)
       ≡ (PB_wand _ _ X (Y : PB))%I).
  { intros <-. apply PB_forall_closed.
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
  {| PBPred := λ Δ, ∀ Δ', X Δ' → Y (Δ ;, Δ')%B |}.
Next Obligation.
  intros X Y D1 D2 H1. by setoid_rewrite H1.
Qed.

Global Instance PB_impl'_proper : Proper ((≡) ==> (≡) ==> (≡)) PB_impl'.
Proof. compute; naive_solver. Qed.

Global Instance PB_impl_Is_closed (X : PB) (Y : C) :
  Is_closed Fint (PB_impl' X (Y : PB)).
Proof.
  apply Is_closed_inc.
  change (from_closure.cl bunch comma formula Fint) with cl.
  (* change (cl (PB_impl' X Y) ⊢@{PB_alg} X → (Y : PB)). *)
  cut (PB_forall _ ({ Δ | X Δ } * { ϕ : formula | (Y : PB) ⊢@{PB_alg} Fint ϕ })
               (λ '(Δ, ϕ), Fint' (IMPL (collapse (`Δ)) (`ϕ)) : PB)
       ≡ (PB_impl' X Y)%I).
  { intros <-. apply PB_forall_closed.
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

Program Definition C_impl (X Y : C) := {| CPred := PB_impl' X Y |}.

Lemma is_heyting_impl (X Y Z : C) :
  ((X : PB) ⊢@{PB_alg} (PB_impl' Y Z : PB)) ↔
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

Program Definition C_alg : bi :=
  C_alg bunch comma formula Fint C_impl _ _ _ .
Next Obligation.
  intros X1 X2 HX Y1 Y2 HY. split.
  - intros Δ. simpl. intros H1 Δ' HX'.
    apply HY. apply H1. apply HX. apply HX'.
  - intros Δ. simpl. intros H1 Δ' HX'.
    apply HY. apply H1. apply HX. apply HX'.
Qed.
Next Obligation. apply is_heyting_impl. Qed.

(** * Interpretation in [C] and Okada's lemma *)
Definition C_atom (a : atom) := Fint' (ATOM a).

Definition inner_interp : formula → C := @formula_interp C_alg C_atom.

(** We verify the Okada's property *)
Lemma okada (A : formula) :
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
      { by apply (IH12 _). }
      simpl. by apply (Hϕ _).
    + intros Δ H1. simpl.
      constructor. apply (IH22 _).
      by apply (H1 _).
Qed.

(** ** Simple structural rules in [C] *)

Lemma bterm_C_refl `{!EqDecision V, !Countable V}
      (T : bterm V) (Xs : V → C_alg) :
  ∀ (Δs : V → bunch),
    (forall (i : V), (Δs i) ∈ (Xs i)) ->
    bterm_ctx_act T Δs ∈ bterm_alg_act T Xs.
Proof.
  intros Δs HΔ.
  induction T; simpl.
  - apply HΔ.
  - apply (cl_unit _ _ _). do 2 eexists.
    repeat split; last reflexivity.
    + apply IHT1.
    + apply IHT2.
  - split.
    + by apply C_weaken.
    + rewrite comm. by apply C_weaken.
Qed.

(** An alternative description of the closed sets `T[Xs]` for linear terms

<<
     T[Xs] = cl { T[Δs] | ∀ i, Δs i ∈ Xs i }
>>
*)
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
  - intros Δ HXs. apply (cl_unit _ _ _).
    exists (λ (i : V),
            match decide (i = x) with
            | left _ => Δ
            | right _ => frml BOT
            end).
    rewrite /= decide_True//.
    split; last done.
    intros i. case_decide; simplify_eq/=; auto.
    apply C_inhabited.
  - simpl in TL.
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
    apply (cl_unit _ _ _). simpl.
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
  - simpl in TL.
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
    eapply (Hϕ _).
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

(** All the simple structural rules are valid in [C] *)
Lemma C_extensions (Ts : list (bterm nat)) (T : bterm nat) :
    (Ts, T) ∈ M.rules → rule_valid C_alg Ts T.
Proof.
  intros Hs. unfold rule_valid.
  intros Xs.
  trans (bterm_alg_act (PROP:=C_alg) T
        (λ i, cl' (CPred' (Xs i)))).
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
  intros Ti HTi. simpl. apply (Hϕ _).
  exists (Ti ↾ HTi). simpl. eapply bterm_C_refl.
  intros i. specialize (HΔs i). revert HΔs.
  simpl. generalize (Xs i)=>X. apply X.
Qed.

(** * Cut admissibility *)
Theorem cut Γ Δ ϕ ψ :
  (Δ ⊢ᴮ ψ) →
  (fill Γ (frml ψ) ⊢ᴮ ϕ) →
  fill Γ Δ ⊢ᴮ ϕ.
Proof.
  intros H1%(seq_interp_sound (PROP:=C_alg) C_atom); last first.
  { apply C_extensions. }
  intros H2%(seq_interp_sound (PROP:=C_alg) C_atom); last first.
  { apply C_extensions. }
  change (seq_interp C_atom Δ ψ) with (bunch_interp C_atom Δ ⊢@{C_alg} formula_interp C_atom ψ) in H1.
  change (seq_interp C_atom (fill Γ (frml ψ)) ϕ) with
    (bunch_interp C_atom (fill Γ (frml ψ)) ⊢@{C_alg} formula_interp C_atom ϕ) in H2.
  cut (@seq_interp C_alg C_atom (fill Γ Δ) ϕ).
  { simpl. intros H3.
    destruct (okada ϕ) as [Hϕ1 Hϕ2].
    apply (Hϕ2 _). unfold inner_interp.
    apply H3. apply (C_collapse_inv _ [] (fill Γ Δ)). simpl.
    apply (bunch_interp_collapse C_alg C_atom).
    apply okada. }
  simpl. rewrite -H2.
  apply bunch_interp_fill_mono, H1.
Qed.

(* Print Assumptions cut. *)
(* ==> Depends only on rules and rules_good *)
