From iris.algebra Require Import monoid.
From iris_mod.bi Require Export interface derived_connectives.
From iris.prelude Require Import options.

(* The sections add [BiAffine] and the like, which is only picked up with [Type*]. *)
Set Default Proof Using "Type*".

(** Naming schema for lemmas about modalities:
    M1_into_M2: M1 P ⊢ M2 P
    M1_M2_elim: M1 (M2 P) ⊣⊢ M1 P
    M1_elim_M2: M1 (M2 P) ⊣⊢ M2 P
    M1_M2: M1 (M2 P) ⊣⊢ M2 (M1 P)
*)

Module bi.
Import interface.bi.
Section derived.
Context {PROP : bi}.
Implicit Types φ : Prop.
Implicit Types P Q R : PROP.
Implicit Types Ps : list PROP.
Implicit Types A : Type.

Local Hint Extern 100 (NonExpansive _) => solve_proper : core.

(* Force implicit argument PROP *)
Notation "P ⊢ Q" := (P ⊢@{PROP} Q).
Notation "P ⊣⊢ Q" := (P ⊣⊢@{PROP} Q).

(* Derived stuff about the entailment *)
Global Instance entails_anti_sym : AntiSymm (⊣⊢) (@bi_entails PROP).
Proof. intros P Q ??. by apply equiv_entails. Qed.
Lemma equiv_entails_1_1 P Q : (P ⊣⊢ Q) → (P ⊢ Q).
Proof. apply equiv_entails. Qed.
Lemma equiv_entails_1_2 P Q : (P ⊣⊢ Q) → (Q ⊢ P).
Proof. apply equiv_entails. Qed.
Lemma equiv_entails_2 P Q : (P ⊢ Q) → (Q ⊢ P) → (P ⊣⊢ Q).
Proof. intros. by apply equiv_entails. Qed.

Global Instance entails_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> iff) ((⊢) : relation PROP).
Proof.
  move => P1 P2 /equiv_entails [HP1 HP2] Q1 Q2 /equiv_entails [HQ1 HQ2]; split=>?.
  - by trans P1; [|trans Q1].
  - by trans P2; [|trans Q2].
Qed.
Lemma entails_equiv_l P Q R : (P ⊣⊢ Q) → (Q ⊢ R) → (P ⊢ R).
Proof. by intros ->. Qed.
Lemma entails_equiv_r P Q R : (P ⊢ Q) → (Q ⊣⊢ R) → (P ⊢ R).
Proof. by intros ? <-. Qed.
Global Instance bi_emp_valid_proper : Proper ((⊣⊢) ==> iff) (@bi_emp_valid PROP).
Proof. solve_proper. Qed.
Global Instance bi_emp_valid_mono : Proper ((⊢) ==> impl) (@bi_emp_valid PROP).
Proof. solve_proper. Qed.
Global Instance bi_emp_valid_flip_mono :
  Proper (flip (⊢) ==> flip impl) (@bi_emp_valid PROP).
Proof. solve_proper. Qed.

(* Propers *)
Global Instance pure_proper : Proper (iff ==> (⊣⊢)) (@bi_pure PROP) | 0.
Proof. intros φ1 φ2 Hφ. apply equiv_dist=> n. by apply pure_ne. Qed.
Global Instance and_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_and PROP) := ne_proper_2 _.
Global Instance or_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_or PROP) := ne_proper_2 _.
Global Instance impl_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_impl PROP) := ne_proper_2 _.
Global Instance sep_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_sep PROP) := ne_proper_2 _.
Global Instance wand_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_wand PROP) := ne_proper_2 _.
Global Instance forall_proper A :
  Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (@bi_forall PROP A).
Proof.
  intros Φ1 Φ2 HΦ. apply equiv_dist=> n.
  apply forall_ne=> x. apply equiv_dist, HΦ.
Qed.
Global Instance exist_proper A :
  Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (@bi_exist PROP A).
Proof.
  intros Φ1 Φ2 HΦ. apply equiv_dist=> n.
  apply exist_ne=> x. apply equiv_dist, HΦ.
Qed.

(* Derived logical stuff *)
Lemma and_elim_l' P Q R : (P ⊢ R) → P ∧ Q ⊢ R.
Proof. by rewrite and_elim_l. Qed.
Lemma and_elim_r' P Q R : (Q ⊢ R) → P ∧ Q ⊢ R.
Proof. by rewrite and_elim_r. Qed.
Lemma or_intro_l' P Q R : (P ⊢ Q) → P ⊢ Q ∨ R.
Proof. intros ->; apply or_intro_l. Qed.
Lemma or_intro_r' P Q R : (P ⊢ R) → P ⊢ Q ∨ R.
Proof. intros ->; apply or_intro_r. Qed.
Lemma exist_intro' {A} P (Ψ : A → PROP) a : (P ⊢ Ψ a) → P ⊢ ∃ a, Ψ a.
Proof. intros ->; apply exist_intro. Qed.
Lemma forall_elim' {A} P (Ψ : A → PROP) : (P ⊢ ∀ a, Ψ a) → ∀ a, P ⊢ Ψ a.
Proof. move=> HP a. by rewrite HP forall_elim. Qed.

Local Hint Resolve pure_intro forall_intro : core.
Local Hint Resolve or_elim or_intro_l' or_intro_r' : core.
Local Hint Resolve and_intro and_elim_l' and_elim_r' : core.

Lemma impl_intro_l P Q R : (Q ∧ P ⊢ R) → P ⊢ Q → R.
Proof. intros HR; apply impl_intro_r; rewrite -HR; auto. Qed.
Lemma impl_elim P Q R : (P ⊢ Q → R) → (P ⊢ Q) → P ⊢ R.
Proof. intros. rewrite -(impl_elim_l' P Q R); auto. Qed.
Lemma impl_elim_r' P Q R : (Q ⊢ P → R) → P ∧ Q ⊢ R.
Proof. intros; apply impl_elim with P; auto. Qed.
Lemma impl_elim_l P Q : (P → Q) ∧ P ⊢ Q.
Proof. by apply impl_elim_l'. Qed.
Lemma impl_elim_r P Q : P ∧ (P → Q) ⊢ Q.
Proof. by apply impl_elim_r'. Qed.

Lemma False_elim P : False ⊢ P.
Proof. by apply (pure_elim' False). Qed.
Lemma True_intro P : P ⊢ True.
Proof. by apply pure_intro. Qed.
Local Hint Immediate False_elim : core.

Lemma entails_eq_True P Q : (P ⊢ Q) ↔ ((P → Q)%I ≡ True%I).
Proof.
  split=>EQ.
  - apply bi.equiv_entails; split; [by apply True_intro|].
    apply impl_intro_r. rewrite and_elim_r //.
  - trans (P ∧ True)%I.
    + apply and_intro; first done. by apply pure_intro.
    + rewrite -EQ impl_elim_r. done.
Qed.
Lemma entails_impl_True P Q : (P ⊢ Q) ↔ (True ⊢ (P → Q)).
Proof. rewrite entails_eq_True equiv_entails; naive_solver. Qed.

Lemma and_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∧ P' ⊢ Q ∧ Q'.
Proof. auto. Qed.
Lemma and_mono_l P P' Q : (P ⊢ Q) → P ∧ P' ⊢ Q ∧ P'.
Proof. by intros; apply and_mono. Qed.
Lemma and_mono_r P P' Q' : (P' ⊢ Q') → P ∧ P' ⊢ P ∧ Q'.
Proof. by apply and_mono. Qed.

Lemma or_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∨ P' ⊢ Q ∨ Q'.
Proof. auto. Qed.
Lemma or_mono_l P P' Q : (P ⊢ Q) → P ∨ P' ⊢ Q ∨ P'.
Proof. by intros; apply or_mono. Qed.
Lemma or_mono_r P P' Q' : (P' ⊢ Q') → P ∨ P' ⊢ P ∨ Q'.
Proof. by apply or_mono. Qed.

Lemma impl_mono P P' Q Q' : (Q ⊢ P) → (P' ⊢ Q') → (P → P') ⊢ Q → Q'.
Proof.
  intros HP HQ'; apply impl_intro_l; rewrite -HQ'.
  apply impl_elim with P; eauto.
Qed.
Lemma forall_mono {A} (Φ Ψ : A → PROP) :
  (∀ a, Φ a ⊢ Ψ a) → (∀ a, Φ a) ⊢ ∀ a, Ψ a.
Proof.
  intros HP. apply forall_intro=> a; rewrite -(HP a); apply forall_elim.
Qed.
Lemma exist_mono {A} (Φ Ψ : A → PROP) :
  (∀ a, Φ a ⊢ Ψ a) → (∃ a, Φ a) ⊢ ∃ a, Ψ a.
Proof. intros HΦ. apply exist_elim=> a; rewrite (HΦ a); apply exist_intro. Qed.

Global Instance and_mono' : Proper ((⊢) ==> (⊢) ==> (⊢)) (@bi_and PROP).
Proof. by intros P P' HP Q Q' HQ; apply and_mono. Qed.
Global Instance and_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢) ==> flip (⊢)) (@bi_and PROP).
Proof. by intros P P' HP Q Q' HQ; apply and_mono. Qed.
Global Instance or_mono' : Proper ((⊢) ==> (⊢) ==> (⊢)) (@bi_or PROP).
Proof. by intros P P' HP Q Q' HQ; apply or_mono. Qed.
Global Instance or_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢) ==> flip (⊢)) (@bi_or PROP).
Proof. by intros P P' HP Q Q' HQ; apply or_mono. Qed.
Global Instance impl_mono' :
  Proper (flip (⊢) ==> (⊢) ==> (⊢)) (@bi_impl PROP).
Proof. by intros P P' HP Q Q' HQ; apply impl_mono. Qed.
Global Instance impl_flip_mono' :
  Proper ((⊢) ==> flip (⊢) ==> flip (⊢)) (@bi_impl PROP).
Proof. by intros P P' HP Q Q' HQ; apply impl_mono. Qed.
Global Instance forall_mono' A :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (@bi_forall PROP A).
Proof. intros P1 P2; apply forall_mono. Qed.
Global Instance forall_flip_mono' A :
  Proper (pointwise_relation _ (flip (⊢)) ==> flip (⊢)) (@bi_forall PROP A).
Proof. intros P1 P2; apply forall_mono. Qed.
Global Instance exist_mono' A :
  Proper (pointwise_relation _ ((⊢)) ==> (⊢)) (@bi_exist PROP A).
Proof. intros P1 P2; apply exist_mono. Qed.
Global Instance exist_flip_mono' A :
  Proper (pointwise_relation _ (flip (⊢)) ==> flip (⊢)) (@bi_exist PROP A).
Proof. intros P1 P2; apply exist_mono. Qed.

Global Instance and_idem : IdemP (⊣⊢) (@bi_and PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_idem : IdemP (⊣⊢) (@bi_or PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance and_comm : Comm (⊣⊢) (@bi_and PROP).
Proof. intros P Q; apply (anti_symm (⊢)); auto. Qed.
Global Instance True_and : LeftId (⊣⊢) True%I (@bi_and PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance and_True : RightId (⊣⊢) True%I (@bi_and PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance False_and : LeftAbsorb (⊣⊢) False%I (@bi_and PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance and_False : RightAbsorb (⊣⊢) False%I (@bi_and PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance True_or : LeftAbsorb (⊣⊢) True%I (@bi_or PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_True : RightAbsorb (⊣⊢) True%I (@bi_or PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance False_or : LeftId (⊣⊢) False%I (@bi_or PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_False : RightId (⊣⊢) False%I (@bi_or PROP).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance and_assoc : Assoc (⊣⊢) (@bi_and PROP).
Proof. intros P Q R; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_comm : Comm (⊣⊢) (@bi_or PROP).
Proof. intros P Q; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_assoc : Assoc (⊣⊢) (@bi_or PROP).
Proof. intros P Q R; apply (anti_symm (⊢)); auto. Qed.
Global Instance True_impl : LeftId (⊣⊢) True%I (@bi_impl PROP).
Proof.
  intros P; apply (anti_symm (⊢)).
  - by rewrite -(left_id True%I (∧)%I (_ → _)%I) impl_elim_r.
  - by apply impl_intro_l; rewrite left_id.
Qed.

Lemma False_impl P : (False → P) ⊣⊢ True.
Proof.
  apply (anti_symm (⊢)); [by auto|].
  apply impl_intro_l. rewrite left_absorb. auto.
Qed.

Lemma exist_impl_forall {A} P (Ψ : A → PROP) :
  ((∃ x : A, Ψ x) → P) ⊣⊢ ∀ x : A, Ψ x → P.
Proof.
  apply equiv_entails; split.
  - apply forall_intro=>x. by rewrite -exist_intro.
  - apply impl_intro_r, impl_elim_r', exist_elim=>x.
    apply impl_intro_r. by rewrite (forall_elim x) impl_elim_r.
Qed.
Lemma forall_unit (Ψ : unit → PROP) :
  (∀ x, Ψ x) ⊣⊢ Ψ ().
Proof.
  apply (anti_symm (⊢)).
  - rewrite (forall_elim ()) //.
  - apply forall_intro=>[[]]. done.
Qed.
Lemma exist_unit (Ψ : unit → PROP) :
  (∃ x, Ψ x) ⊣⊢ Ψ ().
Proof.
  apply (anti_symm (⊢)).
  - apply exist_elim=>[[]]. done.
  - rewrite -(exist_intro ()). done.
Qed.

Lemma exist_exist {A B} (Ψ : A → B → PROP) :
  (∃ x y, Ψ x y) ⊣⊢ (∃ y x, Ψ x y).
Proof.
  apply (anti_symm (⊢));
    do 2 (apply exist_elim=>?); rewrite -2!exist_intro; eauto.
Qed.
Lemma forall_forall {A B} (Ψ : A → B → PROP) :
  (∀ x y, Ψ x y) ⊣⊢ (∀ y x, Ψ x y).
Proof.
  apply (anti_symm (⊢));
    do 2 (apply forall_intro=>?); rewrite 2!forall_elim; eauto.
Qed.
Lemma exist_forall {A B} (Ψ : A → B → PROP) :
  (∃ x, ∀ y, Ψ x y) ⊢ (∀ y, ∃ x, Ψ x y).
Proof.
  apply forall_intro=>?. apply exist_elim=>?.
  rewrite -exist_intro forall_elim ; eauto.
Qed.

Lemma impl_curry P Q R : (P → Q → R) ⊣⊢ (P ∧ Q → R).
Proof.
  apply (anti_symm _).
  - apply impl_intro_l. by rewrite (comm _ P) -and_assoc !impl_elim_r.
  - do 2 apply impl_intro_l. by rewrite assoc (comm _ Q) impl_elim_r.
Qed.

Lemma or_and_l P Q R : P ∨ Q ∧ R ⊣⊢ (P ∨ Q) ∧ (P ∨ R).
Proof.
  apply (anti_symm (⊢)); first auto.
  do 2 (apply impl_elim_l', or_elim; apply impl_intro_l); auto.
Qed.
Lemma or_and_r P Q R : P ∧ Q ∨ R ⊣⊢ (P ∨ R) ∧ (Q ∨ R).
Proof. by rewrite -!(comm _ R) or_and_l. Qed.
Lemma and_or_l P Q R : P ∧ (Q ∨ R) ⊣⊢ P ∧ Q ∨ P ∧ R.
Proof.
  apply (anti_symm (⊢)); last auto.
  apply impl_elim_r', or_elim; apply impl_intro_l; auto.
Qed.
Lemma and_or_r P Q R : (P ∨ Q) ∧ R ⊣⊢ P ∧ R ∨ Q ∧ R.
Proof. by rewrite -!(comm _ R) and_or_l. Qed.
Lemma and_exist_l {A} P (Ψ : A → PROP) : P ∧ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∧ Ψ a.
Proof.
  apply (anti_symm (⊢)).
  - apply impl_elim_r'. apply exist_elim=>a. apply impl_intro_l.
    by rewrite -(exist_intro a).
  - apply exist_elim=>a. apply and_intro; first by rewrite and_elim_l.
    by rewrite -(exist_intro a) and_elim_r.
Qed.
Lemma and_exist_r {A} P (Φ: A → PROP) : (∃ a, Φ a) ∧ P ⊣⊢ ∃ a, Φ a ∧ P.
Proof.
  rewrite -(comm _ P) and_exist_l. apply exist_proper=>a. by rewrite comm.
Qed.
Lemma or_exist {A} (Φ Ψ : A → PROP) :
  (∃ a, Φ a ∨ Ψ a) ⊣⊢ (∃ a, Φ a) ∨ (∃ a, Ψ a).
Proof.
  apply (anti_symm (⊢)).
  - apply exist_elim=> a. by rewrite -!(exist_intro a).
  - apply or_elim; apply exist_elim=> a; rewrite -(exist_intro a); auto.
Qed.

Lemma and_alt P Q : P ∧ Q ⊣⊢ ∀ b : bool, if b then P else Q.
Proof.
   apply (anti_symm _); first apply forall_intro=> -[]; auto.
   by apply and_intro; [rewrite (forall_elim true)|rewrite (forall_elim false)].
Qed.
Lemma or_alt P Q : P ∨ Q ⊣⊢ ∃ b : bool, if b then P else Q.
Proof.
  apply (anti_symm _); last apply exist_elim=> -[]; auto.
  by apply or_elim; [rewrite -(exist_intro true)|rewrite -(exist_intro false)].
Qed.

Lemma entails_equiv_and P Q : (P ⊣⊢ Q ∧ P) ↔ (P ⊢ Q).
Proof.
  split.
  - intros ->; auto.
  - intros; apply (anti_symm _); auto.
Qed.

Global Instance iff_ne : NonExpansive2 (@bi_iff PROP).
Proof. unfold bi_iff; solve_proper. Qed.
Global Instance iff_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_iff PROP) := ne_proper_2 _.

Lemma iff_refl Q P : Q ⊢ P ↔ P.
Proof. rewrite /bi_iff; apply and_intro; apply impl_intro_l; auto. Qed.
Lemma iff_sym P Q : (P ↔ Q) ⊣⊢ (Q ↔ P).
Proof.
  apply equiv_entails. split; apply and_intro;
    try apply and_elim_r; apply and_elim_l.
Qed.


(* BI Stuff *)
Local Hint Resolve sep_mono : core.
Lemma sep_mono_l P P' Q : (P ⊢ Q) → P ∗ P' ⊢ Q ∗ P'.
Proof. by intros; apply sep_mono. Qed.
Lemma sep_mono_r P P' Q' : (P' ⊢ Q') → P ∗ P' ⊢ P ∗ Q'.
Proof. by apply sep_mono. Qed.
Global Instance sep_mono' : Proper ((⊢) ==> (⊢) ==> (⊢)) (@bi_sep PROP).
Proof. by intros P P' HP Q Q' HQ; apply sep_mono. Qed.
Global Instance sep_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢) ==> flip (⊢)) (@bi_sep PROP).
Proof. by intros P P' HP Q Q' HQ; apply sep_mono. Qed.
Lemma wand_mono P P' Q Q' : (Q ⊢ P) → (P' ⊢ Q') → (P -∗ P') ⊢ Q -∗ Q'.
Proof.
  intros HP HQ; apply wand_intro_r. rewrite HP -HQ. by apply wand_elim_l'.
Qed.
Global Instance wand_mono' : Proper (flip (⊢) ==> (⊢) ==> (⊢)) (@bi_wand PROP).
Proof. by intros P P' HP Q Q' HQ; apply wand_mono. Qed.
Global Instance wand_flip_mono' :
  Proper ((⊢) ==> flip (⊢) ==> flip (⊢)) (@bi_wand PROP).
Proof. by intros P P' HP Q Q' HQ; apply wand_mono. Qed.

Global Instance sep_comm : Comm (⊣⊢) (@bi_sep PROP).
Proof. intros P Q; apply (anti_symm _); auto using sep_comm'. Qed.
Global Instance sep_assoc : Assoc (⊣⊢) (@bi_sep PROP).
Proof.
  intros P Q R; apply (anti_symm _); auto using sep_assoc'.
  by rewrite !(comm _ P) !(comm _ _ R) sep_assoc'.
Qed.
Global Instance emp_sep : LeftId (⊣⊢) emp%I (@bi_sep PROP).
Proof. intros P; apply (anti_symm _); auto using emp_sep_1, emp_sep_2. Qed.
Global Instance sep_emp : RightId (⊣⊢) emp%I (@bi_sep PROP).
Proof. by intros P; rewrite comm left_id. Qed.

Global Instance sep_False : LeftAbsorb (⊣⊢) False%I (@bi_sep PROP).
Proof. intros P; apply (anti_symm _); auto using wand_elim_l'. Qed.
Global Instance False_sep : RightAbsorb (⊣⊢) False%I (@bi_sep PROP).
Proof. intros P. by rewrite comm left_absorb. Qed.

Lemma True_sep_2 P : P ⊢ True ∗ P.
Proof. rewrite -{1}[P](left_id emp%I bi_sep). auto using sep_mono. Qed.
Lemma sep_True_2 P : P ⊢ P ∗ True.
Proof. by rewrite comm -True_sep_2. Qed.

Lemma sep_intro_emp_valid_l P Q R : (⊢ P) → (R ⊢ Q) → R ⊢ P ∗ Q.
Proof. intros ? ->. rewrite -{1}(left_id emp%I _ Q). by apply sep_mono. Qed.
Lemma sep_intro_emp_valid_r P Q R : (R ⊢ P) → (⊢ Q) → R ⊢ P ∗ Q.
Proof. intros -> ?. rewrite comm. by apply sep_intro_emp_valid_l. Qed.
Lemma sep_elim_emp_valid_l P Q R : (⊢ P) → (P ∗ R ⊢ Q) → R ⊢ Q.
Proof. intros <- <-. by rewrite left_id. Qed.
Lemma sep_elim_emp_valid_r P Q R : (⊢P) → (R ∗ P ⊢ Q) → R ⊢ Q.
Proof. intros <- <-. by rewrite right_id. Qed.

Lemma wand_intro_l P Q R : (Q ∗ P ⊢ R) → P ⊢ Q -∗ R.
Proof. rewrite comm; apply wand_intro_r. Qed.
Lemma wand_elim_l P Q : (P -∗ Q) ∗ P ⊢ Q.
Proof. by apply wand_elim_l'. Qed.
Lemma wand_elim_r P Q : P ∗ (P -∗ Q) ⊢ Q.
Proof. rewrite (comm _ P); apply wand_elim_l. Qed.
Lemma wand_elim_r' P Q R : (Q ⊢ P -∗ R) → P ∗ Q ⊢ R.
Proof. intros ->; apply wand_elim_r. Qed.
Lemma wand_apply P Q R S : (P ⊢ Q -∗ R) → (S ⊢ P ∗ Q) → S ⊢ R.
Proof. intros HR%wand_elim_l' HQ. by rewrite HQ. Qed.
Lemma wand_frame_l P Q R : (Q -∗ R) ⊢ P ∗ Q -∗ P ∗ R.
Proof. apply wand_intro_l. rewrite -assoc. apply sep_mono_r, wand_elim_r. Qed.
Lemma wand_frame_r P Q R : (Q -∗ R) ⊢ Q ∗ P -∗ R ∗ P.
Proof.
  apply wand_intro_l. rewrite ![(_ ∗ P)%I]comm -assoc.
  apply sep_mono_r, wand_elim_r.
Qed.

Global Instance emp_wand : LeftId (⊣⊢) emp%I (@bi_wand PROP).
Proof.
  intros P. apply (anti_symm _).
  - by rewrite -[(emp -∗ P)%I]left_id wand_elim_r.
  - apply wand_intro_l. by rewrite left_id.
Qed.

Lemma False_wand P : (False -∗ P) ⊣⊢ True.
Proof.
  apply (anti_symm (⊢)); [by auto|].
  apply wand_intro_l. rewrite left_absorb. auto.
Qed.

Lemma wand_trans P Q R : (P -∗ Q) ∗ (Q -∗ R) ⊢ (P -∗ R).
Proof. apply wand_intro_l. by rewrite assoc !wand_elim_r. Qed.

Lemma wand_curry P Q R : (P -∗ Q -∗ R) ⊣⊢ (P ∗ Q -∗ R).
Proof.
  apply (anti_symm _).
  - apply wand_intro_l. by rewrite (comm _ P) -assoc !wand_elim_r.
  - do 2 apply wand_intro_l. by rewrite assoc (comm _ Q) wand_elim_r.
Qed.

Lemma sep_and_l P Q R : P ∗ (Q ∧ R) ⊢ (P ∗ Q) ∧ (P ∗ R).
Proof. auto. Qed.
Lemma sep_and_r P Q R : (P ∧ Q) ∗ R ⊢ (P ∗ R) ∧ (Q ∗ R).
Proof. auto. Qed.
Lemma sep_or_l P Q R : P ∗ (Q ∨ R) ⊣⊢ (P ∗ Q) ∨ (P ∗ R).
Proof.
  apply (anti_symm (⊢)); last by eauto 8.
  apply wand_elim_r', or_elim; apply wand_intro_l; auto.
Qed.
Lemma sep_or_r P Q R : (P ∨ Q) ∗ R ⊣⊢ (P ∗ R) ∨ (Q ∗ R).
Proof. by rewrite -!(comm _ R) sep_or_l. Qed.
Lemma sep_exist_l {A} P (Ψ : A → PROP) : P ∗ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∗ Ψ a.
Proof.
  intros; apply (anti_symm (⊢)).
  - apply wand_elim_r', exist_elim=>a. apply wand_intro_l.
    by rewrite -(exist_intro a).
  - apply exist_elim=> a; apply sep_mono; auto using exist_intro.
Qed.
Lemma sep_exist_r {A} (Φ: A → PROP) Q: (∃ a, Φ a) ∗ Q ⊣⊢ ∃ a, Φ a ∗ Q.
Proof. setoid_rewrite (comm _ _ Q); apply sep_exist_l. Qed.
Lemma sep_forall_l {A} P (Ψ : A → PROP) : P ∗ (∀ a, Ψ a) ⊢ ∀ a, P ∗ Ψ a.
Proof. by apply forall_intro=> a; rewrite forall_elim. Qed.
Lemma sep_forall_r {A} (Φ : A → PROP) Q : (∀ a, Φ a) ∗ Q ⊢ ∀ a, Φ a ∗ Q.
Proof. by apply forall_intro=> a; rewrite forall_elim. Qed.

Lemma exist_wand_forall {A} P (Ψ : A → PROP) :
  ((∃ x : A, Ψ x) -∗ P) ⊣⊢ ∀ x : A, Ψ x -∗ P.
Proof.
  apply equiv_entails; split.
  - apply forall_intro=>x. by rewrite -exist_intro.
  - apply wand_intro_r, wand_elim_r', exist_elim=>x.
    apply wand_intro_r. by rewrite (forall_elim x) wand_elim_r.
Qed.

Global Instance wand_iff_ne : NonExpansive2 (@bi_wand_iff PROP).
Proof. solve_proper. Qed.
Global Instance wand_iff_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_wand_iff PROP) := ne_proper_2 _.

Lemma wand_iff_refl P : emp ⊢ P ∗-∗ P.
Proof. apply and_intro; apply wand_intro_l; by rewrite right_id. Qed.

Lemma wand_entails P Q : (⊢ P -∗ Q) → P ⊢ Q.
Proof. intros. rewrite -[P]emp_sep. by apply wand_elim_l'. Qed.
Lemma entails_wand P Q : (P ⊢ Q) → ⊢ P -∗ Q.
Proof. intros ->. apply wand_intro_r. by rewrite left_id. Qed.
(* A version that works with rewrite, in which bi_emp_valid is unfolded. *)
Lemma entails_wand' P Q : (P ⊢ Q) → emp ⊢ (P -∗ Q).
Proof. apply entails_wand. Qed.
Lemma wand_entails' P Q : (emp ⊢ (P -∗ Q)) → P ⊢ Q.
Proof. apply wand_entails. Qed.

Lemma equiv_wand_iff P Q : (P ⊣⊢ Q) → ⊢ P ∗-∗ Q.
Proof. intros ->; apply wand_iff_refl. Qed.
Lemma wand_iff_equiv P Q : (⊢ P ∗-∗ Q) → (P ⊣⊢ Q).
Proof.
  intros HPQ; apply (anti_symm (⊢));
    apply wand_entails; rewrite /bi_emp_valid HPQ /bi_wand_iff; auto.
Qed.
Lemma wand_iff_sym P Q :
  (P ∗-∗ Q) ⊣⊢ (Q ∗-∗ P).
Proof.
  apply equiv_entails; split; apply and_intro;
    try apply and_elim_r; apply and_elim_l.
Qed.

Lemma entails_impl P Q : (P ⊢ Q) → (⊢ P → Q).
Proof. intros ->. apply impl_intro_l. auto. Qed.
Lemma impl_entails P Q `{!Affine P} : (⊢ P → Q) → P ⊢ Q.
Proof. intros HPQ. apply impl_elim with P=>//. by rewrite {1}(affine P). Qed.

Lemma equiv_iff P Q : (P ⊣⊢ Q) → (⊢ P ↔ Q).
Proof. intros ->; apply iff_refl. Qed.
Lemma iff_equiv P Q `{!Affine P, !Affine Q} : (⊢ P ↔ Q)%I → (P ⊣⊢ Q).
Proof.
  intros HPQ; apply (anti_symm (⊢));
    apply: impl_entails; rewrite /bi_emp_valid HPQ /bi_iff; auto.
Qed.

Lemma and_parallel P1 P2 Q1 Q2 :
  (P1 ∧ P2) -∗ ((P1 -∗ Q1) ∧ (P2 -∗ Q2)) -∗ Q1 ∧ Q2.
Proof.
  apply wand_intro_r, and_intro.
  - rewrite !and_elim_l wand_elim_r. done.
  - rewrite !and_elim_r wand_elim_r. done.
Qed.

Lemma wandM_sound (mP : option PROP) Q :
  (mP -∗? Q) ⊣⊢ (default emp mP -∗ Q).
Proof. destruct mP; simpl; first done. rewrite emp_wand //. Qed.

(* Pure stuff *)
Lemma pure_elim φ Q R : (Q ⊢ ⌜φ⌝) → (φ → Q ⊢ R) → Q ⊢ R.
Proof.
  intros HQ HQR. rewrite -(idemp (∧)%I Q) {1}HQ.
  apply impl_elim_l', pure_elim'=> ?. apply impl_intro_l.
  rewrite and_elim_l; auto.
Qed.
Lemma pure_mono φ1 φ2 : (φ1 → φ2) → ⌜φ1⌝ ⊢ ⌜φ2⌝.
Proof. auto using pure_elim', pure_intro. Qed.
Global Instance pure_mono' : Proper (impl ==> (⊢)) (@bi_pure PROP).
Proof. intros φ1 φ2; apply pure_mono. Qed.
Global Instance pure_flip_mono : Proper (flip impl ==> flip (⊢)) (@bi_pure PROP).
Proof. intros φ1 φ2; apply pure_mono. Qed.
Lemma pure_iff φ1 φ2 : (φ1 ↔ φ2) → ⌜φ1⌝ ⊣⊢ ⌜φ2⌝.
Proof. intros [??]; apply (anti_symm _); auto using pure_mono. Qed.
Lemma pure_elim_l φ Q R : (φ → Q ⊢ R) → ⌜φ⌝ ∧ Q ⊢ R.
Proof. intros; apply pure_elim with φ; eauto. Qed.
Lemma pure_elim_r φ Q R : (φ → Q ⊢ R) → Q ∧ ⌜φ⌝ ⊢ R.
Proof. intros; apply pure_elim with φ; eauto. Qed.

Lemma pure_True (φ : Prop) : φ → ⌜φ⌝ ⊣⊢ True.
Proof. intros; apply (anti_symm _); auto. Qed.
Lemma pure_False (φ : Prop) : ¬φ → ⌜φ⌝ ⊣⊢ False.
Proof. intros; apply (anti_symm _); eauto using pure_mono. Qed.

Lemma pure_and φ1 φ2 : ⌜φ1 ∧ φ2⌝ ⊣⊢ ⌜φ1⌝ ∧ ⌜φ2⌝.
Proof.
  apply (anti_symm _).
  - apply and_intro; apply pure_mono; tauto.
  - eapply (pure_elim φ1); [auto|]=> ?. rewrite and_elim_r. auto using pure_mono.
Qed.
Lemma pure_or φ1 φ2 : ⌜φ1 ∨ φ2⌝ ⊣⊢ ⌜φ1⌝ ∨ ⌜φ2⌝.
Proof.
  apply (anti_symm _).
  - eapply pure_elim=> // -[?|?]; auto using pure_mono.
  - apply or_elim; eauto using pure_mono.
Qed.
Lemma pure_impl_1 φ1 φ2 : ⌜φ1 → φ2⌝ ⊢ (⌜φ1⌝ → ⌜φ2⌝).
Proof. apply impl_intro_l. rewrite -pure_and. apply pure_mono. naive_solver. Qed.
Lemma pure_forall_1 {A} (φ : A → Prop) : ⌜∀ x, φ x⌝ ⊢ ∀ x, ⌜φ x⌝.
Proof. apply forall_intro=> x. eauto using pure_mono. Qed.
Lemma pure_exist {A} (φ : A → Prop) : ⌜∃ x, φ x⌝ ⊣⊢ ∃ x, ⌜φ x⌝.
Proof.
  apply (anti_symm _).
  - eapply pure_elim=> // -[x ?]. rewrite -(exist_intro x); auto using pure_mono.
  - apply exist_elim=> x. eauto using pure_mono.
Qed.

Lemma pure_impl_forall φ P : (⌜φ⌝ → P) ⊣⊢ (∀ _ : φ, P).
Proof.
  apply (anti_symm _).
  - apply forall_intro=> ?. by rewrite pure_True // left_id.
  - apply impl_intro_l, pure_elim_l=> Hφ. by rewrite (forall_elim Hφ).
Qed.
Lemma pure_alt φ : ⌜φ⌝ ⊣⊢ ∃ _ : φ, True.
Proof.
  apply (anti_symm _).
  - eapply pure_elim; eauto=> H. rewrite -(exist_intro H); auto.
  - by apply exist_elim, pure_intro.
Qed.
Lemma pure_wand_forall φ P `{!Absorbing P} : (⌜φ⌝ -∗ P) ⊣⊢ (∀ _ : φ, P).
Proof.
  apply (anti_symm _).
  - apply forall_intro=> Hφ.
    rewrite -(pure_intro φ emp) // emp_wand //.
  - apply wand_intro_l, wand_elim_l', pure_elim'=> Hφ.
    apply wand_intro_l. rewrite (forall_elim Hφ) comm. by apply absorbing.
Qed.

(* Properties of the affinely modality *)
Global Instance affinely_ne : NonExpansive (@bi_affinely PROP).
Proof. solve_proper. Qed.
Global Instance affinely_proper : Proper ((⊣⊢) ==> (⊣⊢)) (@bi_affinely PROP).
Proof. solve_proper. Qed.
Global Instance affinely_mono' : Proper ((⊢) ==> (⊢)) (@bi_affinely PROP).
Proof. solve_proper. Qed.
Global Instance affinely_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_affinely PROP).
Proof. solve_proper. Qed.

Lemma affinely_elim_emp P : <affine> P ⊢ emp.
Proof. rewrite /bi_affinely; auto. Qed.
Lemma affinely_elim P : <affine> P ⊢ P.
Proof. rewrite /bi_affinely; auto. Qed.
Lemma affinely_mono P Q : (P ⊢ Q) → <affine> P ⊢ <affine> Q.
Proof. by intros ->. Qed.
Lemma affinely_idemp P : <affine> <affine> P ⊣⊢ <affine> P.
Proof. by rewrite /bi_affinely assoc idemp. Qed.

Lemma affinely_intro' P Q : (<affine> P ⊢ Q) → <affine> P ⊢ <affine> Q.
Proof. intros <-. by rewrite affinely_idemp. Qed.

Lemma affinely_False : <affine> False ⊣⊢ False.
Proof. by rewrite /bi_affinely right_absorb. Qed.
Lemma affinely_emp : <affine> emp ⊣⊢ emp.
Proof. by rewrite /bi_affinely (idemp bi_and). Qed.
Lemma affinely_or P Q : <affine> (P ∨ Q) ⊣⊢ <affine> P ∨ <affine> Q.
Proof. by rewrite /bi_affinely and_or_l. Qed.
Lemma affinely_and P Q : <affine> (P ∧ Q) ⊣⊢ <affine> P ∧ <affine> Q.
Proof.
  rewrite /bi_affinely -(comm _ P) (assoc _ (_ ∧ _)%I) -!(assoc _ P).
  by rewrite idemp !assoc (comm _ P).
Qed.
Lemma affinely_sep_2 P Q : <affine> P ∗ <affine> Q ⊢ <affine> (P ∗ Q).
Proof.
  rewrite /bi_affinely. apply and_intro.
  - by rewrite !and_elim_l right_id.
  - by rewrite !and_elim_r.
Qed.
Lemma affinely_forall {A} (Φ : A → PROP) : <affine> (∀ a, Φ a) ⊢ ∀ a, <affine> (Φ a).
Proof. apply forall_intro=> a. by rewrite (forall_elim a). Qed.
Lemma affinely_exist {A} (Φ : A → PROP) : <affine> (∃ a, Φ a) ⊣⊢ ∃ a, <affine> (Φ a).
Proof. by rewrite /bi_affinely and_exist_l. Qed.

Lemma affinely_True_emp : <affine> True ⊣⊢ <affine> emp.
Proof. apply (anti_symm _); rewrite /bi_affinely; auto. Qed.

Lemma affinely_and_l P Q : <affine> P ∧ Q ⊣⊢ <affine> (P ∧ Q).
Proof. by rewrite /bi_affinely assoc. Qed.
Lemma affinely_and_r P Q : P ∧ <affine> Q ⊣⊢ <affine> (P ∧ Q).
Proof. by rewrite /bi_affinely !assoc (comm _ P). Qed.
Lemma affinely_and_lr P Q : <affine> P ∧ Q ⊣⊢ P ∧ <affine> Q.
Proof. by rewrite affinely_and_l affinely_and_r. Qed.

(* Properties of the absorbingly modality *)
Global Instance absorbingly_ne : NonExpansive (@bi_absorbingly PROP).
Proof. solve_proper. Qed.
Global Instance absorbingly_proper : Proper ((⊣⊢) ==> (⊣⊢)) (@bi_absorbingly PROP).
Proof. solve_proper. Qed.
Global Instance absorbingly_mono' : Proper ((⊢) ==> (⊢)) (@bi_absorbingly PROP).
Proof. solve_proper. Qed.
Global Instance absorbingly_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_absorbingly PROP).
Proof. solve_proper. Qed.

Lemma absorbingly_intro P : P ⊢ <absorb> P.
Proof. by rewrite /bi_absorbingly -True_sep_2. Qed.
Lemma absorbingly_mono P Q : (P ⊢ Q) → <absorb> P ⊢ <absorb> Q.
Proof. by intros ->. Qed.
Lemma absorbingly_idemp P : <absorb> <absorb> P ⊣⊢ <absorb> P.
Proof.
  apply (anti_symm _), absorbingly_intro.
  rewrite /bi_absorbingly assoc. apply sep_mono; auto.
Qed.

Lemma absorbingly_pure φ : <absorb> ⌜ φ ⌝ ⊣⊢ ⌜ φ ⌝.
Proof.
  apply (anti_symm _), absorbingly_intro.
  apply wand_elim_r', pure_elim'=> ?. apply wand_intro_l; auto.
Qed.
Lemma absorbingly_or P Q : <absorb> (P ∨ Q) ⊣⊢ <absorb> P ∨ <absorb> Q.
Proof. by rewrite /bi_absorbingly sep_or_l. Qed.
Lemma absorbingly_and_1 P Q : <absorb> (P ∧ Q) ⊢ <absorb> P ∧ <absorb> Q.
Proof. apply and_intro; apply absorbingly_mono; auto. Qed.
Lemma absorbingly_forall {A} (Φ : A → PROP) : <absorb> (∀ a, Φ a) ⊢ ∀ a, <absorb> (Φ a).
Proof. apply forall_intro=> a. by rewrite (forall_elim a). Qed.
Lemma absorbingly_exist {A} (Φ : A → PROP) : <absorb> (∃ a, Φ a) ⊣⊢ ∃ a, <absorb> (Φ a).
Proof. by rewrite /bi_absorbingly sep_exist_l. Qed.

Lemma absorbingly_sep P Q : <absorb> (P ∗ Q) ⊣⊢ <absorb> P ∗ <absorb> Q.
Proof. by rewrite -{1}absorbingly_idemp /bi_absorbingly !assoc -!(comm _ P) !assoc. Qed.
Lemma absorbingly_True_emp : <absorb> True ⊣⊢ <absorb> emp.
Proof. by rewrite absorbingly_pure /bi_absorbingly right_id. Qed.
Lemma absorbingly_wand P Q : <absorb> (P -∗ Q) ⊢ <absorb> P -∗ <absorb> Q.
Proof. apply wand_intro_l. by rewrite -absorbingly_sep wand_elim_r. Qed.

Lemma absorbingly_sep_l P Q : <absorb> P ∗ Q ⊣⊢ <absorb> (P ∗ Q).
Proof. by rewrite /bi_absorbingly assoc. Qed.
Lemma absorbingly_sep_r P Q : P ∗ <absorb> Q ⊣⊢ <absorb> (P ∗ Q).
Proof. by rewrite /bi_absorbingly !assoc (comm _ P). Qed.
Lemma absorbingly_sep_lr P Q : <absorb> P ∗ Q ⊣⊢ P ∗ <absorb> Q.
Proof. by rewrite absorbingly_sep_l absorbingly_sep_r. Qed.

(* Affine and absorbing propositions *)
Global Instance Affine_proper : Proper ((⊣⊢) ==> iff) (@Affine PROP).
Proof. solve_proper. Qed.
Global Instance Absorbing_proper : Proper ((⊣⊢) ==> iff) (@Absorbing PROP).
Proof. solve_proper. Qed.

Lemma affine_affinely P `{!Affine P} : <affine> P ⊣⊢ P.
Proof. rewrite /bi_affinely. apply (anti_symm _); auto. Qed.
Lemma absorbing_absorbingly P `{!Absorbing P} : <absorb> P ⊣⊢ P.
Proof. by apply (anti_symm _), absorbingly_intro. Qed.

Lemma True_affine_all_affine P : Affine (PROP:=PROP) True → Affine P.
Proof. rewrite /Affine=> <-; auto. Qed.
Lemma emp_absorbing_all_absorbing P : Absorbing (PROP:=PROP) emp → Absorbing P.
Proof.
  intros. rewrite /Absorbing -{2}(emp_sep P).
  rewrite -(absorbing emp) absorbingly_sep_l left_id //.
Qed.

Lemma sep_elim_l P Q `{HQP : TCOr (Affine Q) (Absorbing P)} : P ∗ Q ⊢ P.
Proof.
  destruct HQP.
  - by rewrite (affine Q) right_id.
  - by rewrite (True_intro Q) comm.
Qed.
Lemma sep_elim_r P Q `{TCOr (Affine P) (Absorbing Q)} : P ∗ Q ⊢ Q.
Proof. by rewrite comm sep_elim_l. Qed.

Lemma sep_and P Q :
  TCOr (Affine P) (Absorbing Q) → TCOr (Absorbing P) (Affine Q) →
  P ∗ Q ⊢ P ∧ Q.
Proof.
  intros [?|?] [?|?];
    apply and_intro; apply: sep_elim_l || apply: sep_elim_r.
Qed.

Lemma affinely_intro P Q `{!Affine P} : (P ⊢ Q) → P ⊢ <affine> Q.
Proof. intros <-. by rewrite affine_affinely. Qed.

Lemma emp_and P `{!Affine P} : emp ∧ P ⊣⊢ P.
Proof. apply (anti_symm _); auto. Qed.
Lemma and_emp P `{!Affine P} : P ∧ emp ⊣⊢ P.
Proof. apply (anti_symm _); auto. Qed.
Lemma emp_or P `{!Affine P} : emp ∨ P ⊣⊢ emp.
Proof. apply (anti_symm _); auto. Qed.
Lemma or_emp P `{!Affine P} : P ∨ emp ⊣⊢ emp.
Proof. apply (anti_symm _); auto. Qed.

Lemma True_sep P `{!Absorbing P} : True ∗ P ⊣⊢ P.
Proof. apply (anti_symm _); auto using True_sep_2. Qed.
Lemma sep_True P `{!Absorbing P} : P ∗ True ⊣⊢ P.
Proof. by rewrite comm True_sep. Qed.


(* Conditional affinely modality *)
Global Instance affinely_if_ne p : NonExpansive (@bi_affinely_if PROP p).
Proof. solve_proper. Qed.
Global Instance affinely_if_proper p : Proper ((⊣⊢) ==> (⊣⊢)) (@bi_affinely_if PROP p).
Proof. solve_proper. Qed.
Global Instance affinely_if_mono' p : Proper ((⊢) ==> (⊢)) (@bi_affinely_if PROP p).
Proof. solve_proper. Qed.
Global Instance affinely_if_flip_mono' p :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_affinely_if PROP p).
Proof. solve_proper. Qed.

Lemma affinely_if_mono p P Q : (P ⊢ Q) → <affine>?p P ⊢ <affine>?p Q.
Proof. by intros ->. Qed.
Lemma affinely_if_flag_mono (p q : bool) P : (q → p) → <affine>?p P ⊢ <affine>?q P.
Proof. destruct p, q; naive_solver auto using affinely_elim. Qed.

Lemma affinely_if_elim p P : <affine>?p P ⊢ P.
Proof. destruct p; simpl; auto using affinely_elim. Qed.
Lemma affinely_affinely_if p P : <affine> P ⊢ <affine>?p P.
Proof. destruct p; simpl; auto using affinely_elim. Qed.
Lemma affinely_if_intro' p P Q : (<affine>?p P ⊢ Q) → <affine>?p P ⊢ <affine>?p Q.
Proof. destruct p; simpl; auto using affinely_intro'. Qed.

Lemma affinely_if_emp p : <affine>?p emp ⊣⊢ emp.
Proof. destruct p; simpl; auto using affinely_emp. Qed.
Lemma affinely_if_and p P Q : <affine>?p (P ∧ Q) ⊣⊢ <affine>?p P ∧ <affine>?p Q.
Proof. destruct p; simpl; auto using affinely_and. Qed.
Lemma affinely_if_or p P Q : <affine>?p (P ∨ Q) ⊣⊢ <affine>?p P ∨ <affine>?p Q.
Proof. destruct p; simpl; auto using affinely_or. Qed.
Lemma affinely_if_exist {A} p (Ψ : A → PROP) :
  <affine>?p (∃ a, Ψ a) ⊣⊢ ∃ a, <affine>?p (Ψ a).
Proof. destruct p; simpl; auto using affinely_exist. Qed.
Lemma affinely_if_sep_2 p P Q : <affine>?p P ∗ <affine>?p Q ⊢ <affine>?p (P ∗ Q).
Proof. destruct p; simpl; auto using affinely_sep_2. Qed.

Lemma affinely_if_idemp p P : <affine>?p <affine>?p P ⊣⊢ <affine>?p P.
Proof. destruct p; simpl; auto using affinely_idemp. Qed.

Lemma affinely_if_and_l p P Q : <affine>?p P ∧ Q ⊣⊢ <affine>?p (P ∧ Q).
Proof. destruct p; simpl; auto using affinely_and_l. Qed.
Lemma affinely_if_and_r p P Q : P ∧ <affine>?p Q ⊣⊢ <affine>?p (P ∧ Q).
Proof. destruct p; simpl; auto using affinely_and_r. Qed.
Lemma affinely_if_and_lr p P Q : <affine>?p P ∧ Q ⊣⊢ P ∧ <affine>?p Q.
Proof. destruct p; simpl; auto using affinely_and_lr. Qed.

(* Conditional absorbingly modality *)
Global Instance absorbingly_if_ne p : NonExpansive (@bi_absorbingly_if PROP p).
Proof. solve_proper. Qed.
Global Instance absorbingly_if_proper p : Proper ((⊣⊢) ==> (⊣⊢)) (@bi_absorbingly_if PROP p).
Proof. solve_proper. Qed.
Global Instance absorbingly_if_mono' p : Proper ((⊢) ==> (⊢)) (@bi_absorbingly_if PROP p).
Proof. solve_proper. Qed.
Global Instance absorbingly_if_flip_mono' p :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_absorbingly_if PROP p).
Proof. solve_proper. Qed.

Lemma absorbingly_if_absorbingly p P : <absorb>?p P ⊢ <absorb> P.
Proof. destruct p; simpl; auto using absorbingly_intro. Qed.
Lemma absorbingly_if_intro p P : P ⊢ <absorb>?p P.
Proof. destruct p; simpl; auto using absorbingly_intro. Qed.
Lemma absorbingly_if_mono p P Q : (P ⊢ Q) → <absorb>?p P ⊢ <absorb>?p Q.
Proof. by intros ->. Qed.
Lemma absorbingly_if_flag_mono (p q : bool) P : (p → q) → <absorb>?p P ⊢ <absorb>?q P.
Proof. destruct p, q; try naive_solver auto using absorbingly_intro. Qed.
Lemma absorbingly_if_idemp p P : <absorb>?p <absorb>?p P ⊣⊢ <absorb>?p P.
Proof. destruct p; simpl; auto using absorbingly_idemp. Qed.

Lemma absorbingly_if_pure p φ : <absorb>?p ⌜ φ ⌝ ⊣⊢ ⌜ φ ⌝.
Proof. destruct p; simpl; auto using absorbingly_pure. Qed.
Lemma absorbingly_if_or p P Q : <absorb>?p (P ∨ Q) ⊣⊢ <absorb>?p P ∨ <absorb>?p Q.
Proof. destruct p; simpl; auto using absorbingly_or. Qed.
Lemma absorbingly_if_and_1 p P Q : <absorb>?p (P ∧ Q) ⊢ <absorb>?p P ∧ <absorb>?p Q.
Proof. destruct p; simpl; auto using absorbingly_and_1. Qed.
Lemma absorbingly_if_forall {A} p (Φ : A → PROP) :
  <absorb>?p (∀ a, Φ a) ⊢ ∀ a, <absorb>?p (Φ a).
Proof. destruct p; simpl; auto using absorbingly_forall. Qed.
Lemma absorbingly_if_exist {A} p (Φ : A → PROP) :
  <absorb>?p (∃ a, Φ a) ⊣⊢ ∃ a, <absorb>?p (Φ a).
Proof. destruct p; simpl; auto using absorbingly_exist. Qed.

Lemma absorbingly_if_sep p P Q : <absorb>?p (P ∗ Q) ⊣⊢ <absorb>?p P ∗ <absorb>?p Q.
Proof. destruct p; simpl; auto using absorbingly_sep. Qed.
Lemma absorbingly_if_wand p P Q : <absorb>?p (P -∗ Q) ⊢ <absorb>?p P -∗ <absorb>?p Q.
Proof. destruct p; simpl; auto using absorbingly_wand. Qed.

Lemma absorbingly_if_sep_l p P Q : <absorb>?p P ∗ Q ⊣⊢ <absorb>?p (P ∗ Q).
Proof. destruct p; simpl; auto using absorbingly_sep_l. Qed.
Lemma absorbingly_if_sep_r p P Q : P ∗ <absorb>?p Q ⊣⊢ <absorb>?p (P ∗ Q).
Proof. destruct p; simpl; auto using absorbingly_sep_r. Qed.
Lemma absorbingly_if_sep_lr p P Q : <absorb>?p P ∗ Q ⊣⊢ P ∗ <absorb>?p Q.
Proof. destruct p; simpl; auto using absorbingly_sep_lr. Qed.

(* Affine instances *)
Global Instance emp_affine : Affine (PROP:=PROP) emp.
Proof. by rewrite /Affine. Qed.
Global Instance False_affine : Affine (PROP:=PROP) False.
Proof. by rewrite /Affine False_elim. Qed.
Global Instance and_affine_l P Q : Affine P → Affine (P ∧ Q).
Proof. rewrite /Affine=> ->; auto. Qed.
Global Instance and_affine_r P Q : Affine Q → Affine (P ∧ Q).
Proof. rewrite /Affine=> ->; auto. Qed.
Global Instance or_affine P Q : Affine P → Affine Q → Affine (P ∨ Q).
Proof.  rewrite /Affine=> -> ->; auto. Qed.
Global Instance forall_affine `{Inhabited A} (Φ : A → PROP) :
  (∀ x, Affine (Φ x)) → Affine (∀ x, Φ x).
Proof. intros. rewrite /Affine (forall_elim inhabitant). apply: affine. Qed.
Global Instance exist_affine {A} (Φ : A → PROP) :
  (∀ x, Affine (Φ x)) → Affine (∃ x, Φ x).
Proof. rewrite /Affine=> H. apply exist_elim=> a. by rewrite H. Qed.

Global Instance sep_affine P Q : Affine P → Affine Q → Affine (P ∗ Q).
Proof. rewrite /Affine=>-> ->. by rewrite left_id. Qed.
Global Instance affinely_affine P : Affine (<affine> P).
Proof. rewrite /bi_affinely. apply _. Qed.
Global Instance affinely_if_affine p P : Affine P → Affine (<affine>?p P).
Proof. destruct p; simpl; apply _. Qed.

(* Absorbing instances *)
Global Instance pure_absorbing φ : Absorbing (PROP:=PROP) ⌜φ⌝.
Proof. by rewrite /Absorbing absorbingly_pure. Qed.
Global Instance and_absorbing P Q : Absorbing P → Absorbing Q → Absorbing (P ∧ Q).
Proof. intros. by rewrite /Absorbing absorbingly_and_1 !absorbing. Qed.
Global Instance or_absorbing P Q : Absorbing P → Absorbing Q → Absorbing (P ∨ Q).
Proof. intros. by rewrite /Absorbing absorbingly_or !absorbing. Qed.
Global Instance forall_absorbing {A} (Φ : A → PROP) :
  (∀ x, Absorbing (Φ x)) → Absorbing (∀ x, Φ x).
Proof. rewrite /Absorbing=> ?. rewrite absorbingly_forall. auto using forall_mono. Qed.
Global Instance exist_absorbing {A} (Φ : A → PROP) :
  (∀ x, Absorbing (Φ x)) → Absorbing (∃ x, Φ x).
Proof. rewrite /Absorbing=> ?. rewrite absorbingly_exist. auto using exist_mono. Qed.

Global Instance sep_absorbing_l P Q : Absorbing P → Absorbing (P ∗ Q).
Proof. intros. by rewrite /Absorbing -absorbingly_sep_l absorbing. Qed.
Global Instance sep_absorbing_r P Q : Absorbing Q → Absorbing (P ∗ Q).
Proof. intros. by rewrite /Absorbing -absorbingly_sep_r absorbing. Qed.

Global Instance wand_absorbing_l P Q : Absorbing P → Absorbing (P -∗ Q).
Proof.
  intros. rewrite /Absorbing /bi_absorbingly. apply wand_intro_l.
  by rewrite assoc (sep_elim_l P) wand_elim_r.
Qed.
Global Instance wand_absorbing_r P Q : Absorbing Q → Absorbing (P -∗ Q).
Proof. intros. by rewrite /Absorbing absorbingly_wand !absorbing -absorbingly_intro. Qed.


Global Instance absorbingly_absorbing P : Absorbing (<absorb> P).
Proof. rewrite /bi_absorbingly. apply _. Qed.


(* For big ops *)
Global Instance bi_and_monoid : Monoid (@bi_and PROP) :=
  {| monoid_unit := True%I |}.
Global Instance bi_or_monoid : Monoid (@bi_or PROP) :=
  {| monoid_unit := False%I |}.
Global Instance bi_sep_monoid : Monoid (@bi_sep PROP) :=
  {| monoid_unit := emp%I |}.


(* Limits *)
Lemma limit_preserving_entails {A : ofe} `{Cofe A} (Φ Ψ : A → PROP) :
  NonExpansive Φ → NonExpansive Ψ → LimitPreserving (λ x, Φ x ⊢ Ψ x).
Proof.
  intros HΦ HΨ c Hc. apply entails_eq_True, equiv_dist=>n.
  rewrite conv_compl. apply equiv_dist, entails_eq_True. done.
Qed.
Lemma limit_preserving_equiv {A : ofe} `{Cofe A} (Φ Ψ : A → PROP) :
  NonExpansive Φ → NonExpansive Ψ → LimitPreserving (λ x, Φ x ⊣⊢ Ψ x).
Proof.
  intros HΦ HΨ. eapply limit_preserving_ext.
  { intros x. symmetry; apply equiv_entails. }
  apply limit_preserving_and; by apply limit_preserving_entails.
Qed.
End derived.

End bi.
