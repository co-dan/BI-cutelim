(* Bunched terms *)
From Coq Require Import ssreflect.
From bunched.algebra Require Import bi.
From bunched Require Import syntax interp.
From stdpp Require Import prelude base gmap fin_sets functions.

(** * Bunched terms *)
Inductive bterm (var : Type) : Type :=
| Var (x : var)
| TComma (T1 T2 : bterm var)
| TSemic (T1 T2 : bterm var)
.
Arguments Var {_} x.
Arguments TComma {_} T1 T2.
Arguments TSemic {_} T1 T2.

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

Fixpoint linear_bterm `{!EqDecision V,!Countable V}
  (T : bterm V) : Prop :=
  match T with
  | Var x => True
  | TComma T1 T2
  | TSemic T1 T2 =>
    term_fv T1 ## term_fv T2 ∧
    linear_bterm T1 ∧ linear_bterm T2
  end.

(** We define a "linearization" of a term:
    for a example a term
      (X₁;X₁),X₂
    can be linearized into
      (Y₁;Y₂),Y₃
    with an associated renaming
      { Y₁ => X₁, Y₂ => X₁, Y₃ => X₂ }
   *)
Local Fixpoint linearize_pre (T : bterm nat) (idx : nat) : nat * gmap nat nat * bterm nat :=
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


(** ** Actions on bunches and and interpretation in BI algebras *)
Fixpoint bterm_ctx_act `{!EqDecision V,!Countable V}
         (T : bterm V) (Δs : V → bunch) : bunch :=
  match T with
  | Var v => Δs v
  | TComma T1 T2 => bterm_ctx_act T1 Δs,, bterm_ctx_act T2 Δs
  | TSemic T1 T2 => bterm_ctx_act T1 Δs;, bterm_ctx_act T2 Δs
  end%B.

Fixpoint bterm_alg_act {PROP : bi} `{!EqDecision V,!Countable V}
         (T : bterm V) (Xs : V → PROP) : PROP :=
  match T with
  | Var v => Xs v
  | TComma T1 T2 => bterm_alg_act T1 Xs ∗ bterm_alg_act T2 Xs
  | TSemic T1 T2 => bterm_alg_act T1 Xs ∧ bterm_alg_act T2 Xs
  end%I.

(** * Properties *)

(** On modifications/operations: *)
Lemma bterm_fmap_compose {A B C} (f : A → B) (g : B → C) (T : bterm A) :
  (g ∘ f) <$> T = g <$> (f <$> T).
Proof.
  induction T; simpl; auto.
  - rewrite IHT1 IHT2 //.
  - rewrite IHT1 IHT2 //.
Qed.

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

(** On interpretations/actions of terms: *)

(* Interpretation of bunched terms only depend on free variables *)
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


Definition linearize_bterm_ren_act {PROP : bi} T Xs : nat → PROP := λ (n : nat), Xs (linearize_bterm_ren T !!! n).
Lemma linearize_bterm_act {PROP : bi} (T : bterm nat) (Xs : nat → PROP) :
  bterm_alg_act (linearize_bterm T) (linearize_bterm_ren_act T Xs) ≡ bterm_alg_act T Xs.
Proof.
  rewrite /linearize_bterm_ren_act /linearize_bterm_ren /linearize_bterm.
  generalize 0.
  induction T=>i; simpl.
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

(* XXX: unset the results of loading Equations *)
Global Obligation Tactic := idtac.
(* IMPORTANT: make sure that Equations is loadeded *before* this module, otherwise this will be overwritten. *)
