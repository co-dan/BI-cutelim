(** A BI algebra from a commutative monoid. *)
From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From bunched.algebra Require Import bi.

(** We start with a commutative monoid on a setoid [M] *)
Class Monoid {M : Type} `{!Equiv M} (o : M → M → M) := {
  monoid_unit : M;
  monoid_op_proper :> Proper ((≡) ==> (≡) ==> (≡)) o;
  monoid_assoc :> Assoc (≡) o;
  monoid_comm :> Comm (≡) o;
  monoid_left_id :> LeftId (≡) monoid_unit o;
}.

Section FromMonoid.
  Variable (M : Type) (o : M → M → M).
  Context `{!Equiv M, !Monoid o}.
  Context `{!Equivalence (≡@{M})}.

  Infix "●" := (o) (at level 80, right associativity).

  (** The carrier of the algebra are the predicates on [M] that respect equivalence. *)
  Record PB := MkPB {
    PBPred :> M → Prop;
    PBPred_proper : Proper ((≡) ==> (iff)) PBPred;
  }.
  Arguments MkPB _ {_}.
  Global Existing Instance PBPred_proper.

  Definition PB_entails (X Y : PB) : Prop :=
    ∀ x, X x → Y x.
  Local Infix "⊢" := PB_entails.

  Global Instance PB_equiv : Equiv PB := λ X Y, (X ⊢ Y) ∧ (Y ⊢ X).
  Global Instance PB_equiv_equivalence : Equivalence (≡@{PB}).
  Proof.
    rewrite /equiv /PB_equiv.
    repeat split; repeat intro; naive_solver.
  Qed.


  Program Definition PB_and (X Y : PB) : PB :=
    {| PBPred := (λ x, X x ∧ Y x) |}.
  Next Obligation. solve_proper. Qed.

  Global Instance PB_and_proper : Proper ((≡) ==> (≡) ==> (≡)) PB_and.
  Proof. compute; naive_solver. Qed.

  Program Definition PB_impl (X Y : PB) : PB :=
    {| PBPred := (λ x, X x → Y x) |}.
  Next Obligation.
    intros X Y x x' Hx. rewrite Hx. eauto.
  Qed.

  Global Instance PB_impl_proper : Proper ((≡) ==> (≡) ==> (≡)) PB_impl.
  Proof. compute; naive_solver. Qed.

  Program Definition PB_emp : PB :=
    {| PBPred := (λ x, x ≡ monoid_unit) |}.
  Next Obligation. solve_proper. Qed.

  Program Definition PB_sep (X Y : PB) : PB :=
    {| PBPred := (λ x, ∃ x1 x2, X x1 ∧ Y x2 ∧ (x ≡ (x1 ● x2))) |}.
  Next Obligation. solve_proper. Qed.

  Global Instance PB_sep_proper : Proper ((≡) ==> (≡) ==> (≡)) PB_sep.
  Proof. compute; naive_solver. Qed.

  Program Definition PB_wand (X Y : PB) : PB :=
    @MkPB (λ x, ∀ x1, X x1 → Y (x ● x1)) _.
  Next Obligation.
    intros X Y x x' Hx. by setoid_rewrite Hx.
  Qed.

  Global Instance PB_wand_proper : Proper ((≡) ==> (≡) ==> (≡)) PB_wand.
  Proof. compute; naive_solver. Qed.

  Definition PB_pure (ϕ : Prop) : PB := MkPB (λ _, ϕ).

  Program Definition PB_or (X Y : PB) : PB :=
    {| PBPred := (λ x, X x ∨ Y x) |}.
  Next Obligation. solve_proper. Qed.

  Global Instance PB_or_proper : Proper ((≡) ==> (≡) ==> (≡)) PB_or.
  Proof. compute; naive_solver. Qed.

  Program Definition PB_forall (A : Type) (DD : A → PB) : PB :=
    @MkPB (λ x, ∀ (a : A), DD a x) _.
  Next Obligation.
    intros A DD x x' Hx. by setoid_rewrite Hx.
  Qed.

  Program Definition PB_exists (A : Type) (PBPB : A → PB) : PB :=
    @MkPB (λ x, ∃ (a : A), PBPB a x) _.
  Next Obligation.
    intros A PBPB x x' Hx. by setoid_rewrite Hx.
  Qed.

  Local Notation "'emp'" := PB_emp.
  Local Infix "∗" := PB_sep.
  Local Infix "-∗" := PB_wand.
  Local Infix "∧" := PB_and.

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
    - apply wand_intro_r.
    - apply wand_elim_l'.
  Qed.


  Canonical Structure PB_alg : bi :=
    {| bi_bi_mixin := PB_bi_mixin; |}.

  Global Instance ElemOf_PB : ElemOf M PB := λ a X, X a.

  Global Instance ElemOf_PB_Peoper :
    Proper ((≡) ==> (≡) ==> (≡)) (∈@{PB}).
  Proof.
    intros x1 x2 Hx X1 X2 HX.
    rewrite /elem_of /ElemOf_PB.
    rewrite Hx. split; apply HX.
  Qed.

End FromMonoid.
