(* Bunched terms *)
From Coq Require Import ssreflect.
From bunched.algebra Require Import bi.
From bunched Require Import syntax interp.
From stdpp Require Import prelude base gmap fin_sets functions mapset.

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

(***************************************************)
(** TODO: move this out *)
(** Code by Blaisorblade  *)
From stdpp Require Import finite functions.
Class FiniteDomain {A B M} `{Lookup A B (M B)} (m : M B) := {
  enum_domain : list A;
  finite_mapping (a : A) (b : B) :
    m !! a = Some b -> a ∈ enum_domain;
}.
Arguments enum_domain {A B M _} m {_} : assert.
Section fin_domain.
  Context `{EqDecision B}.
  Context {A M} (m : M B) `{FiniteDomain A B M m}.
  Definition preimage (b : B) : list A :=
    filter (λ a, m !! a = Some b) (enum_domain m).
  Context `{!EqDecision A, !Countable A}.
  Definition preimage_set (b : B) : gset A := list_to_set (preimage b).

  Lemma preimage_eq_1 a b :
    b ∈ preimage a → m !! b = Some a.
  Proof. rewrite /preimage elem_of_list_filter. naive_solver. Qed.

  Lemma preimage_eq_2 a b :
    m !! b = Some a → b ∈ preimage a.
  Proof.
    rewrite /preimage elem_of_list_filter. intros ?; split; auto.
    by eapply finite_mapping.
  Qed.

  Lemma preimage_eq a b :
    b ∈ preimage a ↔ m !! b = Some a.
  Proof. split; [ apply preimage_eq_1 | apply preimage_eq_2 ]. Qed.

  Lemma preimage_set_eq a b :
    b ∈ preimage_set a ↔ m !! b = Some a.
  Proof.
    rewrite /preimage_set elem_of_list_to_set.
    apply preimage_eq.
  Qed.
End fin_domain.

Section finite_preimage.
  Context `{!EqDecision A, !Finite A} {B : Type} (f : A -> B).
  #[local] Set Default Proof Using "Type*".

  (* Instance fn_lookup_total : LookupTotal A B (A -> B) := λ a f, f a. *)
  Instance fn_lookup : Lookup A B (A -> B) := λ a f, Some (f a).
  #[refine] Global Instance finite_finitedomain : FiniteDomain (M := λ B, A -> B) f :=
  { enum_domain := enum _ }.
  Proof. intros; apply elem_of_enum. Defined.
End finite_preimage.

Section map_preimage.
  Context {K A : Type} `{FinMap K M}.
  Context `{!EqDecision A, !Countable A, !EqDecision K, !Countable K}.
  Variable (m : M A).

  #[refine] Global Instance finmapmap_finitedomain : FiniteDomain m :=
  { enum_domain := fst <$> map_to_list m }.
  (* XXX fix set_solver. *)
  Proof. move=> k a /elem_of_map_to_list. apply: elem_of_list_fmap_1. Defined.

End map_preimage.

Section preimage_properties.
  Context `{!EqDecision A, !Countable A, !EqDecision K, !Countable K}.

  Lemma preimage_set_singleton i x : preimage_set ({[ i := x ]} : gmap K A) x ≡ {[i]}.
  Proof.
    intros z. rewrite preimage_set_eq.
    rewrite lookup_singleton_Some. set_solver.
  Qed.

End preimage_properties.
(** / END TODO *)

Global Instance bterm_eqdecision `{EqDecision A} : EqDecision (bterm A).
Proof. solve_decision. Qed.
Global Instance bterm_countable : Countable (bterm nat).
Proof.
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

Definition list_ap {A B} (fs : list (A → B)) (xs : list A) : list B :=
  f ← fs;
  x ← xs;
  [f x].

Section gset_ap.
  Context {A B C : Type}.
  Context `{!EqDecision A, !Countable A, !EqDecision B, !Countable B}.
  Context `{!EqDecision C, !Countable C}.

  Definition set_map_2 (f : A → B → C) (X : gset A) (Y : gset B) : gset C :=
    list_to_set (list_ap (map f (elements X)) (elements Y)).
  Typeclasses Opaque set_map_2.

  Lemma elem_of_map_2 (f : A → B → C) (X : gset A) (Y : gset B) z :
    z ∈ set_map_2 f X Y ↔ ∃ x y, z = f x y ∧ x ∈ X ∧ y ∈ Y.
  Proof.
    unfold set_map_2. rewrite elem_of_list_to_set.
    rewrite /list_ap. rewrite list_fmap_bind.
    rewrite elem_of_list_bind. set_solver.
  Qed.
  (* Global Instance set_unfold_map (f : A → B) (X : C) (P : A → Prop) y : *)
  (*   (∀ x, SetUnfoldElemOf x X (P x)) → *)
  (*   SetUnfoldElemOf y (set_map (D:=D) f X) (∃ x, y = f x ∧ P x). *)
  (* Proof. constructor. rewrite elem_of_map; naive_solver. Qed. *)


End gset_ap.

Global Instance: Params (@set_map_2) 12 := {}.

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

Definition bterm_gset_fmap (f : nat → nat) (T : bterm (gset nat)) : bterm (gset nat) :=
  (λ X, set_map f X) <$> T.
Lemma bterm_gset_fold_fmap (f : nat → nat) (T : bterm (gset nat)) (T' : bterm nat) :
  T' ∈ bterm_gset_fold T → (f <$> T') ∈ (bterm_gset_fold (bterm_gset_fmap f T)).
Proof.
  revert T'; induction T as [X|T1 HT1 T2 HT2|T1 HT1 T2 HT2]=> T' /=.
  - rewrite elem_of_map.
    intros [x [-> Hx]]. simpl.
    rewrite elem_of_map. exists (f x).
    rewrite elem_of_map. eauto.
  - rewrite elem_of_map_2.
    intros (T1' & T2' & -> & HT1' & HT2').
    apply elem_of_map_2. exists (f <$> T1'),(f <$> T2').
    naive_solver.
  - rewrite elem_of_map_2.
    intros (T1' & T2' & -> & HT1' & HT2').
    apply elem_of_map_2. exists (f <$> T1'),(f <$> T2').
    naive_solver.
Qed.
Lemma bterm_gset_fold_fmap_inv (f : nat → gset nat) (T T' : bterm nat) :
  linear_bterm T →
  T' ∈ bterm_gset_fold (f <$> T) → ∃ (g : nat → nat), (∀ i, i ∈ term_fv T → g i ∈ f i) ∧ T' = g <$> T.
Proof.
  revert T'. induction T as [x|T1 HT1 T2 HT2|T1 HT1 T2 HT2]=> T' Hlin /=.
  - rewrite elem_of_map. intros [y [-> Hy]]. exists (const y). split; eauto.
    intros i. simpl. rewrite elem_of_singleton. naive_solver.
  - rewrite elem_of_map_2.
    intros (T1' & T2' & -> & HT1' & HT2').
    destruct Hlin as [Hfv [Hlin1 Hlin2]].
    destruct (HT1 _ Hlin1 HT1') as [g1 [Hg1 ->]].
    destruct (HT2 _ Hlin2 HT2') as [g2 [Hg2 ->]].
    exists (λ i, match (decide (i ∈ term_fv T1)) with left _ => g1 i | right _ => g2 i end).
    split.
    { intros i. rewrite elem_of_union. intros [Hi1 | Hi2].
      - rewrite decide_True //. eauto.
      - rewrite decide_False //.
        { intros ?. specialize (Hfv i). naive_solver. }
        by apply Hg2. }
Admitted.

Section linearize_bterm_properties.
  Context {PROP : bi}.
  Variable (T : bterm nat).
  Implicit Type Xs Ys : nat → PROP.
  Implicit Type n k m : nat.

  Definition linearize_bterm_ren_act Xs : nat → PROP :=
    λ (n : nat), Xs (linearize_bterm_ren T !!! n).

  Definition ren_inverse : nat → gset nat := preimage_set (linearize_bterm_ren T).

  Definition mk_or Xs j (P : PROP) : PROP := (Xs j ∨ P)%I.
  Local Instance mk_or_proper Xs : Proper ((=) ==> (≡) ==> (≡)) (mk_or Xs).
  Proof. Admitted.

  Definition set_disj Xs (s : gset nat) := set_fold (mk_or Xs) False%I s.
  Local Instance set_disj_proper Xs : Proper ((≡) ==> (≡)) (set_disj Xs).
  Proof. Admitted.
  Local Instance set_disj_mono Xs : Proper ((⊆) ==> (⊢)) (set_disj Xs).
  Proof. Admitted.
  Definition disj_ren_inverse Xs : nat → PROP := λ n, set_disj Xs (ren_inverse n).

  Definition transform_premise (Tz : bterm nat) : gset (bterm nat).
  Proof.
    refine (let Tn' := linearize_bterm Tz in _).
    refine (let T'' := bterm_fmap _ _ (λ j, ren_inverse (linearize_bterm_ren Tz !!! j)) Tn' in _).
    apply (bterm_gset_fold T'').
  Defined.

  Lemma linearize_bterm_act Xs :
    bterm_alg_act (linearize_bterm T) Xs ⊢ bterm_alg_act T (disj_ren_inverse Xs).
  Proof.
    rewrite /disj_ren_inverse /ren_inverse /linearize_bterm_ren /linearize_bterm.
    generalize 0.
    induction T as [x | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 ]=>i; simpl.
    - rewrite preimage_set_singleton.
      rewrite /set_disj set_fold_singleton /mk_or. by rewrite right_id.
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
        apply set_disj_mono=>k.
        rewrite !preimage_set_eq. admit. }
      { rewrite IHT2 /=.
        apply bterm_alg_act_mono=>j.
        apply set_disj_mono=>k.
        rewrite !preimage_set_eq. admit. }
  Admitted.

  Lemma bterm_alg_act_renaming'' Tz Xs :
    bterm_alg_act Tz (linearize_bterm_ren_act Xs) ≡ bterm_alg_act ((λ n, linearize_bterm_ren T !!! n) <$> Tz) Xs.
  Proof.
    rewrite /linearize_bterm_ren_act.
    induction Tz as [x | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 ]; eauto; simpl; by f_equiv.
  Qed.

  Lemma ren_ren_inverse i j :
    j ∈ ren_inverse i → linearize_bterm_ren T !!! j = i.
  Proof.
    rewrite /ren_inverse. rewrite preimage_set_eq.
    apply lookup_total_correct.
  Qed.
  (* Lemma ren_inverse_ren i j : *)
  (*   linearize_bterm_ren T !!! j = i → j ∈ ren_inverse i. *)
  (* Proof. *)
  (*   rewrite /ren_inverse. rewrite preimage_set_eq. *)
  (*   intros <-. apply lookup_lookup_total. *)
  (* Qed. *)


  Lemma elem_of_map_ren_ren_inverse x y :
    y ∈ (set_map (C:=gset nat) (λ n, linearize_bterm_ren T !!! n) (ren_inverse x) : gset nat) → y = x.
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
    rewrite -(bterm_fmap_compose (λ j : nat, ren_inverse (linearize_bterm_ren Tz !!! j))).
    rewrite bterm_alg_act_renaming''.
    intros H1. f_equiv.
    revert H1.
    pose (Tz'' := (λ n, linearize_bterm_ren T !!! n) <$> Tz').
    fold Tz''. intros HTz''.
    assert (Tz'' ∈ bterm_gset_fold
                ((λ j : nat, set_map (λ n, linearize_bterm_ren T !!! n) (ren_inverse (linearize_bterm_ren Tz !!! j))) <$> linearize_bterm Tz)) as HH.
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

End linearize_bterm_properties.


(* Definition t0 := (TSemic (TComma (Var 1) (Var 1)) (Var 2)). *)
(* Definition t1 := (TSemic (TComma (Var 1) (Var 2)) (Var 2)). *)
(* Eval compute in (linearize_bterm t0). *)
(* Eval vm_compute in (elements $ ren_inverse t0 0). *)
(* Eval vm_compute in (elements $ transform_premise t0 t1). *)

Definition structural_rule := (list (bterm nat) * bterm nat)%type.

Definition analytic_completion (s : structural_rule) : structural_rule :=
  let '(Ts,T) := s in
  (mjoin $ map (elements ∘ (transform_premise T)) Ts, linearize_bterm T).

(* restricted form of weakening: [a ∗ a ≤ a]
   and it's analytic presentation [a₁ * a₂ ≤ a₁ ∨ a₂] *)
Definition rule_restr_weakn : structural_rule := ([Var 0], TComma (Var 0) (Var 0)).
Definition rule_restr_weakn_a := analytic_completion rule_restr_weakn.
Eval vm_compute in rule_restr_weakn_a.

Definition rule_valid (s : structural_rule) (PROP : bi) : Prop :=
  let '(Ts, T) := s in
  ∀ (Xs : nat → PROP),
    bterm_alg_act T Xs ⊢
       ∃ Ti' : {Ti : bterm nat | Ti ∈ Ts }, bterm_alg_act (proj1_sig Ti') Xs.

Lemma analytic_completion_valid (s : structural_rule) (PROP : bi) :
  rule_valid (analytic_completion s) PROP → rule_valid s PROP.
Proof.
  destruct s as [Ts T].
  rewrite /rule_valid /=. intros H1 Xs.
  rewrite -linearize_bterm_act_ren.
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
  destruct s as [Ts T].
  rewrite /rule_valid /=. intros H1 Xs.
  rewrite linearize_bterm_act.
  rewrite H1. apply bi.exist_elim=>Ti.
  destruct Ti as [Ti HTi]. simpl.
  remember (transform_premise T Ti) as Tzs.
  assert (∃ Tz, Tz ∈ transform_premise T Ti) as [Tz HTz].
  { admit. (* this is not actually true .. *) }
  assert (Tz ∈ mjoin (map (elements ∘ transform_premise T) Ts)) as HTz'.
  { admit. }
  apply (bi.exist_intro' _ _  (Tz ↾ HTz')).
  simpl in *.
  eapply transformed_premise_act_ren in HTz.
  rewrite -HTz.
  admit.
Abort.


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
