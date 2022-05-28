(* Bunched terms *)
From Coq Require Import ssreflect.
From bunched.algebra Require Import bi.
From bunched Require Import syntax interp prelude.sets.
From stdpp Require Import prelude base gmap functions.

(** * Bunched terms *)
Inductive bterm (var : Type) : Type :=
| Var (x : var)
| TComma (T1 T2 : bterm var)
| TSemic (T1 T2 : bterm var)
.
Arguments Var {_} x.
Arguments TComma {_} T1 T2.
Arguments TSemic {_} T1 T2.

Global Instance bterm_eqdecision `{EqDecision A} : EqDecision (bterm A).
Proof. solve_decision. Qed.
Global Instance bterm_countable : Countable (bterm nat).
Proof.
 set (enc :=
   fix go T :=
     match T with
     | Var x => (GenLeaf x : gen_tree nat)
     | TComma T1 T2 => GenNode 0 [go T1; go T2]
     | TSemic T1 T2 => GenNode 1 [go T1; go T2]
     end).
 set (dec :=
   fix go e :=
     match (e : gen_tree nat) with
     | GenLeaf x => Var x
     | GenNode 0 [e1; e2] => TComma (go e1) (go e2)
     | GenNode 1 [e1; e2] => TSemic (go e1) (go e2)
     | _ => Var 0
     end).
 apply (inj_countable' enc dec).
 induction x; simpl; eauto; by rewrite IHx1 IHx2.
Defined.

Fixpoint bterm_alg_act {PROP : bi} `{!EqDecision V,!Countable V}
         (T : bterm V) (Xs : V → PROP) : PROP :=
  match T with
  | Var v => Xs v
  | TComma T1 T2 => bterm_alg_act T1 Xs ∗ bterm_alg_act T2 Xs
  | TSemic T1 T2 => bterm_alg_act T1 Xs ∧ bterm_alg_act T2 Xs
  end%I.

Fixpoint bterm_ctx_act `{!EqDecision V,!Countable V}
         (T : bterm V) (Δs : V → bunch) : bunch :=
  match T with
  | Var v => Δs v
  | TComma T1 T2 => bterm_ctx_act T1 Δs,, bterm_ctx_act T2 Δs
  | TSemic T1 T2 => bterm_ctx_act T1 Δs;, bterm_ctx_act T2 Δs
  end%B.

Global Instance bterm_fmap : FMap bterm :=
  fix go _ _ f T { struct T } := let _ : FMap _ := go in
  match T with
  | Var x => Var (f x)
  | TComma T1 T2 => TComma (f <$> T1) (f <$> T2)
  | TSemic T1 T2 => TSemic (f <$> T1) (f <$> T2)
  end.

Fixpoint term_fv `{!EqDecision V,!Countable V} (T : bterm V) : gset V :=
  match T with
  | Var x => {[ x ]}
  | TComma T1 T2 => term_fv T1 ∪ term_fv T2
  | TSemic T1 T2 => term_fv T1 ∪ term_fv T2
  end.

Fixpoint linear_bterm `{!EqDecision V,!Countable V} (T : bterm V) : Prop :=
  match T with
  | Var x => True
  | TComma T1 T2
  | TSemic T1 T2 =>
    term_fv T1 ## term_fv T2 ∧
    linear_bterm T1 ∧ linear_bterm T2
  end.


(** ** Term linearization *)
(** We define a "linearization" of a term:
    for a example a term
      (X₁;X₁),X₂
    can be linearized into
      (Y₁;Y₂),Y₃
    with an associated renaming
      { Y₁ => X₁, Y₂ => X₁, Y₃ => X₂ }
   *)
Fixpoint linearize_pre (T : bterm nat) (idx : nat) : nat * gmap nat nat * bterm nat :=
  match T with
  | Var x => (idx + 1, {[ idx := x ]}, Var idx)
  | TComma T1 T2 =>
      let '(idx1,m1,T1') := linearize_pre T1 idx in
      let '(idx2,m2,T2') := linearize_pre T2 idx1 in
      (idx2, m1 ∪ m2, TComma T1' T2')
  | TSemic T1 T2 =>
      let '(idx1,m1,T1') := linearize_pre T1 idx in
      let '(idx2,m2,T2') := linearize_pre T2 idx1 in
      (idx2, m1 ∪ m2, TSemic T1' T2')
  end.

Definition linearize_bterm (T : bterm nat) : bterm nat := snd (linearize_pre T 0).
Definition linearize_bterm_ren (T : bterm nat) : gmap nat nat := snd $ fst (linearize_pre T 0).

(** ** Term "folding" *)
Fixpoint bterm_gset_fold (T : bterm (gset nat)) : gset (bterm nat) :=
  match T with
  | Var X => set_map Var X
  | TComma T1 T2 =>
      let S1 := bterm_gset_fold T1 in
      let S2 := bterm_gset_fold T2 in
      set_map_2 TComma S1 S2
  | TSemic T1 T2 =>
      let S1 := bterm_gset_fold T1 in
      let S2 := bterm_gset_fold T2 in
      set_map_2 TSemic S1 S2
  end.

Definition bterm_gset_fmap (f : nat → nat) (T : bterm (gset nat)) : bterm (gset nat) := set_map f <$> T.

(** ** Structural rules *)

Definition structural_rule := (list (bterm nat) * bterm nat)%type.
Definition is_analytical (s : structural_rule) := linear_bterm (snd s).
Definition rule_valid (s : structural_rule) (PROP : bi) : Prop :=
  ∀ (Xs : nat → PROP),
    bterm_alg_act (snd s) Xs ⊢
       ∃ Ti' : {Ti : bterm nat | Ti ∈ fst s }, bterm_alg_act (proj1_sig Ti') Xs.


(** * Properties *)

(** ** fmap properties *)
Lemma bterm_fmap_ext {A B} `{EqDecision A, Countable A} (f g : A → B) (t1 t2 : bterm A) :
  (∀ x, x ∈ term_fv t1 → f x = g x) → t1 = t2 → fmap f t1 = fmap g t2.
Proof.
  intros Hfv <-. induction t1; simpl.
  - f_equal/=. apply Hfv. set_solver.
  - f_equiv/=.
    + apply IHt1_1. set_solver.
    + apply IHt1_2. set_solver.
  - f_equiv/=.
    + apply IHt1_1. set_solver.
    + apply IHt1_2. set_solver.
Qed.

Lemma bterm_fmap_compose {A B C} (f : A → B) (g : B → C) (T : bterm A) :
  (g ∘ f) <$> T = g <$> (f <$> T).
Proof.
  induction T; simpl; auto.
  - rewrite IHT1 IHT2 //.
  - rewrite IHT1 IHT2 //.
Qed.

(** ** interpretation properties *)
Lemma bterm_ctx_act_fv `{!EqDecision V,!Countable V} (T : bterm V) Δs Γs :
  (∀ i : V, i ∈ term_fv T → Δs i = Γs i) →
  bterm_ctx_act T Δs = bterm_ctx_act T Γs.
Proof.
  induction T; simpl.
  - set_solver.
  - set_unfold. intros H.
    rewrite IHT1; eauto. rewrite IHT2; eauto.
  - set_unfold. intros H.
    rewrite IHT1; eauto. rewrite IHT2; eauto.
Qed.
Lemma bterm_alg_act_fv `{!EqDecision V,!Countable V} {PROP : bi}
      (T : bterm V) Δs Γs :
  (∀ i : V, i ∈ term_fv T → Δs i ≡ Γs i) →
  bterm_alg_act T Δs ≡ bterm_alg_act (PROP:=PROP) T Γs.
Proof.
  induction T; simpl.
  - set_solver.
  - set_unfold. intros H.
    rewrite IHT1; eauto. rewrite IHT2; eauto.
  - set_unfold. intros H.
    rewrite IHT1; eauto. rewrite IHT2; eauto.
Qed.

Lemma bterm_alg_act_mono {PROP : bi} `{!EqDecision V, !Countable V}
      (T : bterm V) Xs Ys :
  (∀ i, Xs i ⊢ Ys i) →
  bterm_alg_act T Xs ⊢ bterm_alg_act (PROP:=PROP) T Ys.
Proof.
  intros HXY. induction T; simpl; auto.
  all: by rewrite IHT1 IHT2.
Qed.

Lemma bterm_alg_act_mono' {PROP : bi} `{!EqDecision V, !Countable V}
      (T : bterm V) Xs Ys :
  (∀ i, i ∈ term_fv T → Xs i ⊢ Ys i) →
  bterm_alg_act T Xs ⊢ bterm_alg_act (PROP:=PROP) T Ys.
Proof.
  intros HXY. induction T; simpl; eauto.
  - apply HXY. set_solver.
  - f_equiv.
    + apply IHT1. set_solver.
    + apply IHT2. set_solver.
  - f_equiv.
    + apply IHT1. set_solver.
    + apply IHT2. set_solver.
Qed.

(** Interpretation of bunches is a homomorphism w.r.t. bunched terms:
<<
  ⟦ T(Δs) ⟧ = ⟦ T ⟧ (⟦ Δs ⟧)
>>
*)
Lemma bterm_ctx_alg_act {PROP : bi} `{!EqDecision V,!Countable V}
      (T : bterm V) (Δs : V → bunch) (s : atom → PROP) :
  bunch_interp s (bterm_ctx_act T Δs) =
  bterm_alg_act T (bunch_interp s ∘ Δs).
Proof.
  induction T; simpl.
  - reflexivity.
  - by rewrite IHT1 IHT2.
  - by rewrite IHT1 IHT2.
Qed.

(** Linear bunched terms can be viewed as _bunches with holes_, when
restricted to one free variable. *)
Lemma blinterm_ctx_act_insert `{!EqDecision V, !Countable V} (T : bterm V) Δs i :
  linear_bterm T →
  i ∈ term_fv T →
  ∃ (Π : bunch_ctx), ∀ Γ , fill Π Γ = bterm_ctx_act T (<[i:=Γ]>Δs).
Proof.
  revert i. induction T=>i; simpl ; intros Hlin Hi.
  - exists []. intros Γ. assert ( i = x) as -> by set_solver.
    by rewrite functions.fn_lookup_insert.
  - destruct Hlin as (Hdisj & Hlin1 & Hlin2).
    set_unfold.
    destruct Hi as [Hi1 | Hi2].
    + destruct (IHT1 i Hlin1 Hi1) as (Π₁ & HΠ1).
      exists (Π₁++[CtxCommaL (bterm_ctx_act T2 Δs)]).
      intros Γ. rewrite fill_app /=.
      rewrite HΠ1. f_equiv.
      assert (i ∉ term_fv T2).
      { set_solver. }
      apply bterm_ctx_act_fv.
      intros j. destruct (decide (i = j)) as [->|?].
      { naive_solver. }
      rewrite functions.fn_lookup_insert_ne//.
    + destruct (IHT2 i Hlin2 Hi2) as (Π₁ & HΠ1).
      exists (Π₁++[CtxCommaR (bterm_ctx_act T1 Δs)]).
      intros Γ. rewrite fill_app /=.
      rewrite HΠ1. f_equiv.
      assert (i ∉ term_fv T1).
      { set_solver. }
      apply bterm_ctx_act_fv.
      intros j. destruct (decide (i = j)) as [->|?].
      { naive_solver. }
      rewrite functions.fn_lookup_insert_ne//.
  - destruct Hlin as (Hdisj & Hlin1 & Hlin2).
    set_unfold.
    destruct Hi as [Hi1 | Hi2].
    + destruct (IHT1 i Hlin1 Hi1) as (Π₁ & HΠ1).
      exists (Π₁++[CtxSemicL (bterm_ctx_act T2 Δs)]).
      intros Γ. rewrite fill_app /=.
      rewrite HΠ1. f_equiv.
      assert (i ∉ term_fv T2).
      { set_solver. }
      apply bterm_ctx_act_fv.
      intros j. destruct (decide (i = j)) as [->|?].
      { naive_solver. }
      rewrite functions.fn_lookup_insert_ne//.
    + destruct (IHT2 i Hlin2 Hi2) as (Π₁ & HΠ1).
      exists (Π₁++[CtxSemicR (bterm_ctx_act T1 Δs)]).
      intros Γ. rewrite fill_app /=.
      rewrite HΠ1. f_equiv.
      assert (i ∉ term_fv T1).
      { set_solver. }
      apply bterm_ctx_act_fv.
      intros j. destruct (decide (i = j)) as [->|?].
      { naive_solver. }
      rewrite functions.fn_lookup_insert_ne//.
Qed.

(** ** linearization properties *)
Lemma linearize_pre_mono T (idx1 : nat):
  idx1 ≤ fst $ fst $ linearize_pre T idx1.
Proof.
  revert idx1; induction T=>idx1 /=.
  - lia.
  - specialize (IHT1 idx1).
    destruct (linearize_pre T1 idx1) as [[i1 m1] T1'] eqn:Ht1.
    specialize (IHT2 i1).
    destruct (linearize_pre T2 i1) as [[idx2 m2] T2'] eqn:Ht2.

    simpl in *. lia.
  - specialize (IHT1 idx1).
    destruct (linearize_pre T1 idx1) as [[i1 m1] T1'] eqn:Ht1.
    specialize (IHT2 i1).
    destruct (linearize_pre T2 i1) as [[idx2 m2] T2'] eqn:Ht2.
    simpl in *. lia.
Qed.

Lemma linearize_pre_fv T (idx1 : nat):
  let T' := snd $ linearize_pre T idx1 in
  let idx2 := fst $ fst $ linearize_pre T idx1 in
  term_fv T' ⊆ set_seq idx1 (idx2-idx1).
Proof.
  revert idx1; induction T=>idx1 /=.
  - set_unfold; lia.
  - specialize (IHT1 idx1).
    destruct (linearize_pre T1 idx1) as [[i1 m1] T1'] eqn:Ht1.
    assert (idx1 ≤ i1).
    { replace i1 with (fst $ fst $ linearize_pre T1 idx1); [ | by rewrite Ht1 ].
      apply linearize_pre_mono. }
    specialize (IHT2 i1).
    destruct (linearize_pre T2 i1) as [[idx2 m2] T2'] eqn:Ht2.
    assert (i1 ≤ idx2).
    { replace idx2 with (fst $ fst $ linearize_pre T2 i1); [ | by rewrite Ht2 ].
      apply linearize_pre_mono. }
    simpl. set_solver by lia.
  - specialize (IHT1 idx1).
    destruct (linearize_pre T1 idx1) as [[i1 m1] T1'] eqn:Ht1.
    assert (idx1 ≤ i1).
    { replace i1 with (fst $ fst $ linearize_pre T1 idx1); [ | by rewrite Ht1 ].
      apply linearize_pre_mono. }
    specialize (IHT2 i1).
    destruct (linearize_pre T2 i1) as [[idx2 m2] T2'] eqn:Ht2.
    assert (i1 ≤ idx2).
    { replace idx2 with (fst $ fst $ linearize_pre T2 i1); [ | by rewrite Ht2 ].
      apply linearize_pre_mono. }
    simpl. set_solver by lia.
Qed.

Lemma linearize_pre_dom T (idx1 : nat):
  let idx2 := fst $ fst $ linearize_pre T idx1 in
  let m := snd $ fst $ linearize_pre T idx1 in
  dom (gset nat) m = set_seq idx1 (idx2-idx1).
Proof.
  revert idx1; induction T=>idx1 /=.
  - set_unfold; lia.
  - specialize (IHT1 idx1).
    destruct (linearize_pre T1 idx1) as [[i1 m1] T1'] eqn:Ht1.
    assert (idx1 ≤ i1).
    { replace i1 with (fst $ fst $ linearize_pre T1 idx1); [ | by rewrite Ht1 ].
      apply linearize_pre_mono. }
    specialize (IHT2 i1).
    destruct (linearize_pre T2 i1) as [[idx2 m2] T2'] eqn:Ht2.
    assert (i1 ≤ idx2).
    { replace idx2 with (fst $ fst $ linearize_pre T2 i1); [ | by rewrite Ht2 ].
      apply linearize_pre_mono. }
    simpl in *.
    rewrite dom_union_L IHT1 IHT2.
    set_solver by lia.
  - specialize (IHT1 idx1).
    destruct (linearize_pre T1 idx1) as [[i1 m1] T1'] eqn:Ht1.
    assert (idx1 ≤ i1).
    { replace i1 with (fst $ fst $ linearize_pre T1 idx1); [ | by rewrite Ht1 ].
      apply linearize_pre_mono. }
    specialize (IHT2 i1).
    destruct (linearize_pre T2 i1) as [[idx2 m2] T2'] eqn:Ht2.
    assert (i1 ≤ idx2).
    { replace idx2 with (fst $ fst $ linearize_pre T2 i1); [ | by rewrite Ht2 ].
      apply linearize_pre_mono. }
    simpl in *.
    rewrite dom_union_L IHT1 IHT2.
    set_solver by lia.
Qed.


Lemma linearize_pre_linear T idx :
  linear_bterm (snd $ linearize_pre T idx).
Proof.
  revert idx; induction T=>idx; simpl; eauto.
  - specialize (IHT1 idx).
    destruct (linearize_pre T1 idx) as [[i m1] T1'] eqn:Ht1.
    specialize (IHT2 i).
    destruct (linearize_pre T2 i) as [[idx2 m2] T2'] eqn:Ht2.
    simpl. repeat split; eauto.
    assert (term_fv T1' ⊆ set_seq idx (i-idx)).
    { replace T1' with (snd (linearize_pre T1 idx)) by rewrite Ht1 //.
      replace i with (fst $ fst (linearize_pre T1 idx)) by rewrite Ht1 //.
      apply linearize_pre_fv. }
    assert (term_fv T2' ⊆ set_seq i (idx2-i)).
    { replace T2' with (snd (linearize_pre T2 i)) by rewrite Ht2 //.
      replace idx2 with (fst $ fst (linearize_pre T2 i)) by rewrite Ht2 //.
      apply linearize_pre_fv. }
    set_solver by lia.
  - specialize (IHT1 idx).
    destruct (linearize_pre T1 idx) as [[i m1] T1'] eqn:Ht1.
    specialize (IHT2 i).
    destruct (linearize_pre T2 i) as [[idx2 m2] T2'] eqn:Ht2.
    simpl. repeat split; eauto.
    assert (term_fv T1' ⊆ set_seq idx (i-idx)).
    { replace T1' with (snd (linearize_pre T1 idx)) by rewrite Ht1 //.
      replace i with (fst $ fst (linearize_pre T1 idx)) by rewrite Ht1 //.
      apply linearize_pre_fv. }
    assert (term_fv T2' ⊆ set_seq i (idx2-i)).
    { replace T2' with (snd (linearize_pre T2 i)) by rewrite Ht2 //.
      replace idx2 with (fst $ fst (linearize_pre T2 i)) by rewrite Ht2 //.
      apply linearize_pre_fv. }
    set_solver by lia.
Qed.

(** ** term folding properties *)
Lemma bterm_gset_fold_fmap (f : nat → nat) (T : bterm (gset nat)) (T' : bterm nat) :
  T' ∈ bterm_gset_fold T → f <$> T' ∈ (bterm_gset_fold (bterm_gset_fmap f T)).
Proof.
  revert T'; induction T as [X|T1 HT1 T2 HT2|T1 HT1 T2 HT2]=> T' /=.
  - rewrite elem_of_map.
    intros [x [-> Hx]]. simpl.
    rewrite elem_of_map. exists (f x).
    rewrite elem_of_map. eauto.
  - rewrite sets.elem_of_map_2.
    intros (T1' & T2' & -> & HT1' & HT2').
    apply sets.elem_of_map_2. exists (f <$> T1'),(f <$> T2').
    naive_solver.
  - rewrite sets.elem_of_map_2.
    intros (T1' & T2' & -> & HT1' & HT2').
    apply sets.elem_of_map_2. exists (f <$> T1'),(f <$> T2').
    naive_solver.
Qed.
Lemma bterm_gset_fold_fmap_inv (f : nat → gset nat) (T T' : bterm nat) :
  linear_bterm T →
  T' ∈ bterm_gset_fold (f <$> T) → ∃ (g : nat → nat), (∀ i, i ∈ term_fv T → g i ∈ f i) ∧ T' = g <$> T.
Proof.
  revert T'. induction T as [x|T1 HT1 T2 HT2|T1 HT1 T2 HT2]=> T' Hlin /=.
  - rewrite elem_of_map. intros [y [-> Hy]]. exists (const y). split; eauto.
    intros i. simpl. rewrite elem_of_singleton. naive_solver.
  - rewrite sets.elem_of_map_2.
    intros (T1' & T2' & -> & HT1' & HT2').
    destruct Hlin as [Hfv [Hlin1 Hlin2]].
    destruct (HT1 _ Hlin1 HT1') as [g1 [Hg1 Hg1']].
    destruct (HT2 _ Hlin2 HT2') as [g2 [Hg2 Hg2']].
    exists (λ i, match (decide (i ∈ term_fv T1)) with left _ => g1 i | right _ => g2 i end).
    split.
    { intros i. rewrite elem_of_union. intros [Hi1 | Hi2].
      - rewrite decide_True //. eauto.
      - rewrite decide_False //.
        { intros ?. specialize (Hfv i). naive_solver. }
        by apply Hg2. }
    f_equiv.
    { rewrite Hg1'.
      apply bterm_fmap_ext; auto.
      intros x Hx. rewrite decide_True //. }
    { rewrite Hg2'.
      apply bterm_fmap_ext; auto.
      intros x Hx. assert (x ∉ term_fv T1) by set_solver.
      rewrite decide_False //. }
  - rewrite sets.elem_of_map_2.
    intros (T1' & T2' & -> & HT1' & HT2').
    destruct Hlin as [Hfv [Hlin1 Hlin2]].
    destruct (HT1 _ Hlin1 HT1') as [g1 [Hg1 Hg1']].
    destruct (HT2 _ Hlin2 HT2') as [g2 [Hg2 Hg2']].
    exists (λ i, match (decide (i ∈ term_fv T1)) with left _ => g1 i | right _ => g2 i end).
    split.
    { intros i. rewrite elem_of_union. intros [Hi1 | Hi2].
      - rewrite decide_True //. eauto.
      - rewrite decide_False //.
        { intros ?. specialize (Hfv i). naive_solver. }
        by apply Hg2. }
    f_equiv.
    { rewrite Hg1'.
      apply bterm_fmap_ext; auto.
      intros x Hx. rewrite decide_True //. }
    { rewrite Hg2'.
      apply bterm_fmap_ext; auto.
      intros x Hx. assert (x ∉ term_fv T1) by set_solver.
      rewrite decide_False //. }
Qed.



(* XXX: unset the results of loading Equations *)
Global Obligation Tactic := idtac.
(* IMPORTANT: make sure that Equations is loadeded *before* this module, otherwise this will be overwritten. *)
