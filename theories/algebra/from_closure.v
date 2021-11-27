From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From bunched.algebra Require Import bi from_monoid.

Section FromClosure.
  (** * Algebra carrier *)

  (** Given a BI algebra [P(M)] for a commutative monoid [M] .. *)
  Variable (M : Type) (o : M → M → M).
  Context `{!Equiv M, !Monoid o}.
  Context `{!Equivalence (≡@{M})}.

  Infix "●" := (o) (at level 80, right associativity).

  Definition PB := PB M.
  Definition MkPB := MkPB M.
  Definition PB_alg := PB_alg M o.

  (** We start with a closed basis. *)
  Variable (Basis : Type).
  Variable (basis : Basis → PB).

  (** Here are we are abusing the encoding a little bit;
    the assumption [X ⊆ basis(i)] is external, but we can
    quantifier over its proofs in the type theory. *)
  Program Definition cl (X : PB) : PB :=
    @MkPB (λ m, ∀ (i : Basis), ((X : PB_alg) ⊢ basis i)
                 → basis i m) _.
  Next Obligation.
    intros X i1 i2 HD. by setoid_rewrite HD.
  Qed.

  (** The interior operation *)
  Program Definition int (X : PB) : PB :=
    cl (@MkPB (λ m, ∃ (i : Basis),
               (basis i ⊢@{PB_alg} (X : PB)) ∧ basis i m) _).
  Next Obligation.
    intros X i1 i2 HD. by setoid_rewrite HD.
  Qed.

  Lemma cl_unit X : X ⊢ cl (X : PB_alg).
  Proof.
    intros x Hx. simpl. intros i Hi.
    by apply (Hi x).
  Qed.

  Lemma cl_mono (X Y : PB) : (X ⊢@{PB_alg} Y) → (cl X ⊢@{PB_alg} cl Y).
  Proof.
    intros HX x. simpl. intros H1 i HY.
    eapply H1. by rewrite HX.
  Qed.

  Lemma cl_idemp (X : PB) : cl (cl X) ≡ cl X.
  Proof.
    split; last first.
    { eapply (cl_unit (cl X)). }
    simpl. intros m Hm i Hi.
    eapply (Hm i). intros m' Hm'.
    by eapply (Hm' i).
  Qed.

  Global Instance cl_proper : Proper ((≡) ==> (≡)) cl.
  Proof.
    intros X Y HXY.
    split; eapply (cl_mono _ _); by rewrite HXY.
  Qed.

  Class Is_closed (X : PB) := closed_eq_cl : X ≡ cl X.

  (** Carrier of the algebra are closed sets. *)
  Record C :=
    { CPred :> PB ; CPred_closed : Is_closed CPred }.

  Global Instance C_equiv : Equiv C := (PB_equiv M : Equiv PB).

  Definition C_entails (X Y : C) : Prop := PB_entails M (X : PB) (Y : PB).
  Local Infix "⊢" := C_entails.

  Global Instance ElemOf_C : ElemOf M C := λ a X, (X : PB) a.

  Global Instance ElemOf_C_Proper :
    Proper ((≡) ==> (≡) ==> (≡)) (∈@{C}).
  Proof.
    intros x1 x2 Hx X1 X2 HX.
    rewrite /elem_of /ElemOf_C.
    rewrite Hx. split; apply HX.
  Qed.

  Global Instance ElemOf_C_Proper_1 :
    Proper ((≡) ==> (≡) ==> (impl)) (∈@{C}).
  Proof.
    intros x1 x2 Hx X1 X2 HX.
    rewrite /elem_of /ElemOf_C.
    rewrite Hx.
    unfold impl. apply HX.
  Qed.

  Global Instance ElemOf_C_Proper_2 :
    Proper ((≡) ==> (≡) ==> (flip impl)) (∈@{C}).
  Proof.
    intros x1 x2 Hx X1 X2 HX.
    rewrite /elem_of /ElemOf_C.
    rewrite Hx.
    unfold impl. simpl. apply HX.
  Qed.

  Global Existing Instance CPred_closed.

  Global Instance Is_closed_cl (X : PB) : Is_closed (cl X).
  Proof.
    rewrite /Is_closed. by rewrite cl_idemp.
  Qed.

  (** Specializing [cl : PB → PB] to [PB → C] *)
  Program Definition cl' (X : PB) : C :=
    {| CPred := cl X |}.

  Program Definition int' (X : PB) : C :=
    {| CPred := int X |}.

  Global Instance CPred_proper (X : C) : Proper ((≡) ==> (↔)) (X : PB).
  Proof.
    intros D1 D2 HD.
    by apply PBPred_proper.
  Qed.

  Global Instance C_equiv_equivalence : Equivalence (≡@{C}).
  Proof.
    rewrite /equiv /C_equiv /PB_equiv.
    repeat split; repeat intro; naive_solver.
  Qed.

  Local Instance C_equiv_rr : RewriteRelation (≡@{C}) := {}.


  Global Instance C_entail_proper : Proper ((≡) ==> (≡) ==> (↔)) C_entails.
  Proof.
    intros X1 X2 HX Y1 Y2 HY. unfold C_entails.
    split.
    - intros H1 m HX2.
      by eapply HY, H1, HX.
    - intros H1 m HX1.
      by eapply HY, H1, HX.
  Qed.

  Global Instance Is_closed_proper : Proper ((≡) ==> (↔)) Is_closed.
  Proof.
    intros X Y HXY. unfold Is_closed.
    by rewrite HXY.
  Qed.

  (** * Properties of the closure operator and closed sets *)
  Lemma Is_closed_inc (X : PB) :
    ((cl X : PB_alg) ⊢@{PB_alg} X) → Is_closed X.
  Proof.
    intros H1. unfold Is_closed.
    split.
    - eapply cl_unit.
    - eapply H1.
  Qed.

  Global Instance Is_closed_basis (i : Basis) : Is_closed (basis i).
  Proof.
    apply Is_closed_inc.
    intros m Hcl. simpl. eapply Hcl. eauto.
  Qed.

  Definition basis' i : C :=
    {| CPred := basis i |}.

  Lemma cl_adj (X : PB) (Y : PB) `{!Is_closed Y} :
    (X ⊢@{PB_alg} Y) → cl X ⊢@{PB_alg} Y.
  Proof.
    rewrite (@closed_eq_cl Y).
    rewrite -{2}(cl_idemp Y).
    apply cl_mono.
  Qed.

  Lemma cl'_adj (X : PB) (Y : C) :
    (X ⊢@{PB_alg} (Y : PB)) → cl' X ⊢ Y.
  Proof.
    intros H1. apply cl_adj.
    { apply _. }
    apply H1.
  Qed.

  (* Alternative descriptions of the closure operator, internally in
  the language of the BI algebra *)
  Lemma cl_alt_eq (X : PB) :
    (cl X : PB) ≡
      (∀ Z : { Y : C | X ⊢@{PB_alg} (Y : PB) }, `Z : PB)%I.
  Proof.
    split.
    - simpl. intros m H1.
      rewrite /bi_forall/PB_forall /=.
      intros [[Y HY] HXY]. simpl.
      eapply HY. intros i Hi.
      eapply H1. rewrite -Hi. eapply HXY.
    - simpl. intros m H1 ϕ HX.
      apply (H1 (basis' ϕ ↾ HX)).
  Qed.

  Lemma cl_alt_eq_2 (X : PB) :
    (cl X : PB) ≡
      (∀ Y : C, (⌜X ⊢@{PB_alg} (Y : PB)⌝) → Y : PB)%I.
  Proof.
    rewrite cl_alt_eq.
    split.
    - intros m H1. rewrite /bi_forall /bi_impl /=.
      intros Y HXY. simpl.
      apply (H1 (Y ↾ HXY)).
    - intros m H1. rewrite /bi_forall /bi_impl /=.
      intros [Y HXY]. simpl. apply H1.
      apply HXY.
  Qed.

  (** * Closure strength and the BI operations *)
  Variable impl : C → C → C.
  Hypothesis impl_proper : Proper ((≡) ==> (≡) ==> (≡)) impl.
  Hypothesis (is_heyting_impl : ∀ (X Y Z : C),
        ((X : PB) ⊢@{PB_alg} (impl Y Z : PB)) ↔
          ((X : PB) ∧ (Y : PB) ⊢@{PB_alg} (Z : PB))%I).
  Hypothesis
    (wand_closed : ∀ (X : PB) (Y : C),
        Is_closed (X -∗ (Y : PB))%I).

  Local Instance wand_closed' :
    ∀ (X : PB) (Y : PB), Is_closed Y →
        Is_closed (X -∗ (Y : PB))%I.
  Proof.
    intros X Y HY.
    set (Y' := {| CPred := Y |} : C).
    eapply (wand_closed X Y').
  Qed.

  Lemma cl_strong (X Y : PB) :
    ((cl X) ∗ Y ⊢@{PB_alg} cl (X ∗ Y))%I.
  Proof.
    eapply bi.wand_elim_l'.
    apply cl_adj; first apply _.
    apply bi.wand_intro_r.
    eapply cl_unit.
  Qed.

  (** Universal quantification and conjunciton *)
  Global Instance PB_forall_closed (A : Type) (CC : A → PB) :
    (∀ x : A, Is_closed (CC x)) →
    Is_closed (PB_forall M A CC).
  Proof.
    intros HCC.
    apply Is_closed_inc.
    eapply bi.forall_intro=>a.
    rewrite cl_alt_eq_2.
    rewrite (bi.forall_elim ({| CPred := CC a |})).
    intros m H1. apply H1.
    rewrite /bi_pure /=.
    clear. by rewrite (bi.forall_elim a).
  Qed.

  Definition C_forall (A : Type) (CC : A → C) : C :=
    {| CPred := (∀ x : A, (CC x : PB))%I |}.

  Global Instance PB_and_closed (X Y : PB) :
    Is_closed X →
    Is_closed Y →
    Is_closed (PB_and M X Y).
  Proof.
    intros HX HY.
    apply Is_closed_inc.
    intros m Hm. split.
    + apply HX. intros i H'. eapply Hm.
      rewrite -H'. intros ?. simpl. naive_solver.
    + apply HY. intros i H'. eapply Hm.
      rewrite -H'. intros ?. simpl. naive_solver.
  Qed.

  Definition C_and (X Y : C) : C :=  {| CPred := ((X : PB) ∧ (Y : PB))%I |}.

  (** Disjunction, ex quantification, and multiplication *)
  Definition C_or (X Y : C) : C := cl' (PB_or M (X : PB) (Y : PB)).

  Definition C_exists (A : Type) (CC : A → C) : C := cl' (∃ x : A, CC x : PB)%I.

  Definition C_emp : C := cl' (PB_emp M o).

  Definition C_sep (X Y : C) : C := cl' (PB_sep M o (X : PB) (Y : PB)).

  (** Implications *)
  Definition C_impl (X : C) (Y : C) : C :=
    {| CPred := impl X Y |}.

  Definition C_wand (X : PB) (Y : C) : C :=
    {| CPred := PB_wand M o X (Y : PB) |}.

  (** Embedding Coq propositions *)
  Definition C_pure (ϕ : Prop) : C := cl' (PB_pure M ϕ).

  Local Notation "'emp'" := C_emp.
  Local Infix "∗" := C_sep.
  Local Infix "-∗" := C_wand.
  Local Infix "→" := C_impl.
  Local Infix "∧" := C_and.
  Local Infix "∨" := C_or.

  (** ** BI laws *)
  Global Instance c_entails_preorder : PreOrder C_entails.
  Proof. split; compute; naive_solver. Qed.

  Lemma impl_intro_r (P Q R : C) : (P ∧ Q ⊢ R) → P ⊢ Q → R.
  Proof. apply is_heyting_impl. Qed.
  Lemma impl_elim_l' (P Q R : C) : (P ⊢ Q → R) → P ∧ Q ⊢ R.
  Proof. apply is_heyting_impl. Qed.
  Lemma or_intro_l (P Q : C) : P ⊢ P ∨ Q.
  Proof.
    intros m HP. apply (cl_unit _ m).
    naive_solver.
  Qed.
  Lemma or_intro_r (P Q : C) : Q ⊢ P ∨ Q.
  Proof.
    intros m HP. apply (cl_unit _ m).
    naive_solver.
  Qed.
  Lemma or_elim (P Q R : C) :
    (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
  Proof.
    intros H1 H2.
    apply cl'_adj=>m [?|?]; eauto.
  Qed.
  Lemma sep_mono (P P' Q Q' : C) :
    (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'.
  Proof.
    intros H1 H2 m HP i Hi.
    apply (HP i). clear HP m.
    intros m. destruct 1 as (m1 & m2 & Hm1 & Hm2 & ->).
    eapply (Hi _). do 2 eexists. split; eauto.
  Qed.
  Lemma wand_intro_r (P Q R : C) : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R.
  Proof.
    intros HH m1 HP.
    intros m2 HQ. eapply HH.
    eapply (cl_unit _ _).
    do 2 eexists. repeat split; eauto.
  Qed.
  Lemma wand_elim_l' (P Q R : C) : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R.
  Proof.
    destruct R as [R HR].
    intros HH m HPQ. simpl.
    apply HR. intros i Hi. eapply HPQ.
    clear m HPQ. intros m (m1 & m2 & H1 & H2 & ->).
    apply (Hi _). by apply HH.
  Qed.
  Lemma emp_sep_1 (P : C) : P ⊢ emp ∗ P.
  Proof.
    intros m HP. eapply (cl_unit _ _).
    exists monoid_unit, m. rewrite left_id.
    repeat split; eauto.
    intros i Hi. eapply (Hi _). simpl. reflexivity.
  Qed.
  Lemma emp_sep_2 (P : C) : emp ∗ P ⊢ P.
  Proof.
    apply wand_elim_l'.
    eapply cl'_adj. eapply bi.wand_intro_r.
    apply bi.emp_sep_2.
  Qed.
  Lemma sep_comm' (P Q : C) : P ∗ Q ⊢ Q ∗ P.
  Proof. apply cl_mono. apply bi.sep_comm'. Qed.
  Lemma sep_assoc' (P Q R : C) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
  Proof.
    apply wand_elim_l'.
    apply cl'_adj.
    intros m (D1 & D2 & HD1 & HD2 & ->).
    intros D3 HD3. apply (cl_unit _ _).
    exists D1, (D2 ● D3).
    rewrite (assoc _ D1). repeat split; eauto.
    apply (cl_unit _ _). do 2 eexists; repeat split; eauto.
  Qed.
  Lemma exists_intro {A : Type} (Ψ : A → C) (a : A) :
    Ψ a ⊢ C_exists A Ψ.
  Proof.
    intros m HΨ.
    apply (cl_unit _ _). by exists a.
  Qed.
  Lemma exists_elim {A : Type} (Ψ : A → C) Q :
    (∀ a : A, Ψ a ⊢ Q) → C_exists A Ψ ⊢ Q.
  Proof.
    intros H1 m. apply cl'_adj.
    by apply bi.exist_elim.
  Qed.

  (** [C] satisfies all the BI algebra laws *)
  Lemma C_bi_mixin : BiMixin (PROP:=C)
                              C_entails C_emp C_pure C_and C_or
                              C_impl C_forall C_exists C_sep C_wand.
  Proof.
    split.
    - apply _.
    - apply _.
    - naive_solver.
    - intros A1 A2 HA. compute.
      naive_solver.
    - intros [X1 ?] [X2 ?] [HX1 HX2] [Y1 ?] [Y2 ?] [HY1 HY2].
      split; intro m ; compute in * ; naive_solver.
    - intros X1 X2 HX Y1 Y2 HY; try apply _.
      apply cl_proper.
      split; intro m ; vm_compute in * ; naive_solver.
    - apply impl_proper.
    - intros A P1 P2 HP.
      split; intro m ; vm_compute in * ; naive_solver.
    - intros A P1 P2 HP.
      apply cl_proper.
      split; intro m ; vm_compute in * ; naive_solver.
    - intros X1 X2 HX Y1 Y2 HY; try apply _.
      apply cl_proper.
      split; intro m ; vm_compute in * ; naive_solver.
    - intros X1 X2 HX Y1 Y2 HY; try apply _.
      split; intro m ; vm_compute in * ; naive_solver.
    - (* "Pure" proposition introduction *)
      intros i X Hi m. simpl.
      intros HX j Hs. by apply (Hs _).
    - (* Pure proposition elimination *)
      intros i X Hi.
      apply cl'_adj.
      intros m HHi. apply Hi; eauto.
      intros j Hj. by apply (Hj _).
    - compute; intros; naive_solver.
    - compute; intros; naive_solver.
    - compute; intros; naive_solver.
    - compute; intros; naive_solver.
    - compute; intros; naive_solver.
    - apply or_elim.
    - apply impl_intro_r.
    - apply impl_elim_l'.
    - intros. by apply bi.forall_intro.
    - intros A Ψ a m Hm.
      apply Hm.
    - intros. by apply exists_intro.
    - intros. by apply exists_elim.
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

  (** * Other properties *)

  Lemma impl_from_int (X Y : C) :
    (X → Y) ≡ int' (PB_impl M (X : PB) (Y : PB)).
  Proof. Admitted.

  Lemma cl_sep (X Y : PB) :
    cl' (PB_sep M o X Y) ≡ C_sep (cl' X) (cl' Y).
  Proof.
    rewrite /C_sep.
    split.
    { apply cl_mono. f_equiv; apply cl_unit. }
    cut (cl' (PB_sep M o (cl X) (cl Y)) ⊢ cl' (PB_sep M o X Y)).
    { intros H1 m. apply (H1 m). }
    eapply cl'_adj.
    eapply bi.wand_elim_l'.
    apply (cl'_adj X (cl' Y -∗ cl' (PB_sep M o X Y))).
    apply bi.wand_intro_l.
    apply bi.wand_elim_l'.
    simpl.
    apply cl_adj.
    { apply _. }
    apply bi.wand_intro_l. apply cl_unit.
  Qed.


End FromClosure.

Arguments Is_closed {M} {o} {_} {_} {_} {_} basis X.
Arguments cl_unit {_} {_} {_} {_} {_} {_} basis X. 
