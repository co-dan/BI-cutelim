(** A BI algebra from a commutative monoid. *)
From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From bunched.algebra Require Import bi.

(** We start with a commutative monoid on a setoid [M] *)
Class Monoid (M : Type) `{!Equiv M} (o : M → M → M) := {
  monoid_unit : M;
  monoid_op_proper :> Proper ((≡) ==> (≡) ==> (≡)) o;
  monoid_assoc :> Assoc (≡) o;
  monoid_comm :> Comm (≡) o;
  monoid_left_id :> LeftId (≡) monoid_unit o;
}.

Section FromMonoid.
  Variable (M : Type) (o : M → M → M).
  Context `{!Equiv M, !Monoid M o}.
  Context `{!Equivalence (≡@{M})}.

  Infix "●" := (o) (at level 80, right associativity).

  (** The carrier of the algebra are the predicates on [M] that respect equivalence. *)
  Record PM := MkPM {
    PMPred :> M → Prop;
    PMPred_proper : Proper ((≡) ==> (iff)) PMPred;
  }.
  Arguments MkPM _ {_}.
  Global Existing Instance PMPred_proper.

  Definition PM_entails (X Y : PM) : Prop :=
    ∀ x, X x → Y x.
  Local Infix "⊢" := PM_entails.

  Global Instance PM_equiv : Equiv PM := λ X Y, (X ⊢ Y) ∧ (Y ⊢ X).
  Global Instance PM_equiv_equivalence : Equivalence (≡@{PM}).
  Proof.
    rewrite /equiv /PM_equiv.
    repeat split; repeat intro; naive_solver.
  Qed.


  Program Definition PM_and (X Y : PM) : PM :=
    {| PMPred := (λ x, X x ∧ Y x) |}.
  Next Obligation. solve_proper. Qed.

  Global Instance PM_and_proper : Proper ((≡) ==> (≡) ==> (≡)) PM_and.
  Proof. compute; naive_solver. Qed.

  Program Definition PM_impl (X Y : PM) : PM :=
    {| PMPred := (λ x, X x → Y x) |}.
  Next Obligation.
    intros X Y x x' Hx. rewrite Hx. eauto.
  Qed.

  Global Instance PM_impl_proper : Proper ((≡) ==> (≡) ==> (≡)) PM_impl.
  Proof. compute; naive_solver. Qed.

  Program Definition PM_emp : PM :=
    {| PMPred := (λ x, x ≡ monoid_unit) |}.
  Next Obligation. solve_proper. Qed.

  Program Definition PM_sep (X Y : PM) : PM :=
    {| PMPred := (λ x, ∃ x1 x2, X x1 ∧ Y x2 ∧ (x ≡ (x1 ● x2))) |}.
  Next Obligation. solve_proper. Qed.

  Global Instance PM_sep_proper : Proper ((≡) ==> (≡) ==> (≡)) PM_sep.
  Proof. compute; naive_solver. Qed.

  Program Definition PM_wand (X Y : PM) : PM :=
    @MkPM (λ x, ∀ x1, X x1 → Y (x ● x1)) _.
  Next Obligation.
    intros X Y x x' Hx. by setoid_rewrite Hx.
  Qed.

  Global Instance PM_wand_proper : Proper ((≡) ==> (≡) ==> (≡)) PM_wand.
  Proof. compute; naive_solver. Qed.

  Definition PM_pure (ϕ : Prop) : PM := MkPM (λ _, ϕ).

  Program Definition PM_or (X Y : PM) : PM :=
    {| PMPred := (λ x, X x ∨ Y x) |}.
  Next Obligation. solve_proper. Qed.

  Global Instance PM_or_proper : Proper ((≡) ==> (≡) ==> (≡)) PM_or.
  Proof. compute; naive_solver. Qed.

  Program Definition PM_forall (A : Type) (DD : A → PM) : PM :=
    @MkPM (λ x, ∀ (a : A), DD a x) _.
  Next Obligation.
    intros A DD x x' Hx. by setoid_rewrite Hx.
  Qed.

  Program Definition PM_exists (A : Type) (PMPM : A → PM) : PM :=
    @MkPM (λ x, ∃ (a : A), PMPM a x) _.
  Next Obligation.
    intros A PMPM x x' Hx. by setoid_rewrite Hx.
  Qed.

  Local Notation "'emp'" := PM_emp.
  Local Infix "∗" := PM_sep.
  Local Infix "-∗" := PM_wand.
  Local Infix "∧" := PM_and.

  Lemma sep_mono P P' Q Q' :
    (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'.
  Proof.
    intros H1 H2 x.
    destruct 1 as (x1 & x2 & Hx1 & Hx2 & H3).
    do 2 eexists. repeat split; eauto.
  Qed.
  Lemma emp_sep_1 P : P ⊢ emp ∗ P.
  Proof.
    intros x HP. simpl.
    eexists monoid_unit,_. repeat split.
    - done.
    - eapply HP.
    - by rewrite left_id.
  Qed.
  Lemma emp_sep_2 P : emp ∗ P ⊢ P.
  Proof.
    intros x HP. simpl in HP.
    destruct HP as (x1 & x2 & H1 & H2 & ->).
    rewrite H1. by rewrite left_id.
  Qed.
  Lemma sep_comm' P Q : P ∗ Q ⊢ Q ∗ P.
  Proof.
    intros x (x1 & x2 & H1 & H2 & ->).
    rewrite (comm _ x1 x2).
    do 2 eexists. repeat split; eauto.
  Qed.
  Lemma sep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
  Proof.
    intros x (x1' & x3 & (x1 & x2 & H1 & H2 & H4) & H3 & ->).
    rewrite H4. rewrite -(assoc _ x1 x2 x3).
    do 2 eexists. repeat split; eauto.
    do 2 eexists. repeat split; eauto.
  Qed.
  Lemma wand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R.
  Proof.
    intros HH x HP.
    intros x' HQ. eapply HH.
    do 2 eexists. repeat split; eauto.
  Qed.
  Lemma wand_elim_l' P Q R : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R.
  Proof.
    intros HH x (x1 & x2 & H1 & H2 & ->).
    by eapply HH.
  Qed.

  Global Instance entails_preorder : PreOrder PM_entails.
  Proof. split; compute; naive_solver. Qed.

  Lemma PM_bi_mixin : BiMixin (PROP:=PM)
                              PM_entails PM_emp PM_pure PM_and PM_or
                              PM_impl PM_forall PM_exists PM_sep PM_wand.
  Proof.
    split; try by (compute; naive_solver).
    - apply _.
    - apply _.
    - apply emp_sep_1.
    - apply emp_sep_2.
    - apply sep_comm'.
    - apply sep_assoc'.
    - apply wand_intro_r.
    - apply wand_elim_l'.
  Qed.


  Definition PM_alg : bi :=
    {| bi_bi_mixin := PM_bi_mixin; |}.

  Global Instance ElemOf_PM : ElemOf M PM := λ a X, X a.

  Global Instance ElemOf_PM_Peoper :
    Proper ((≡) ==> (≡) ==> (≡)) (∈@{PM}).
  Proof.
    intros x1 x2 Hx X1 X2 HX.
    rewrite /elem_of /ElemOf_PM.
    rewrite Hx. split; apply HX.
  Qed.

End FromMonoid.
