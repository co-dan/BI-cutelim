From bunched.algebra Require Export interface.
From Coq Require Import ssreflect.
From stdpp Require Import prelude.


Module bi.
Import interface.bi.
Section derived.
Context {PROP : bi}.
Implicit Types φ : Prop.
Implicit Types P Q R : PROP.
Implicit Types Ps : list PROP.
Implicit Types A : Type.

Local Hint Extern 100 (Proper _) => solve_proper : core.

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
Proof. intros φ1 φ2 Hφ. by apply pure_ne. Qed.
Global Instance and_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_and PROP) := _.
Global Instance or_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_or PROP) :=  _.
Global Instance impl_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_impl PROP) :=  _.
Global Instance sep_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_sep PROP) :=  _.
Global Instance wand_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_wand PROP) :=  _.
Global Instance forall_proper A :
  Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (@bi_forall PROP A).
Proof. apply _. Qed.
Global Instance exist_proper A :
  Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (@bi_exist PROP A).
Proof. apply _. Qed.

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

Lemma wand_entails P Q : (⊢ P -∗ Q) → P ⊢ Q.
Proof. intros. rewrite -[P]emp_sep. by apply wand_elim_l'. Qed.
Lemma entails_wand P Q : (P ⊢ Q) → ⊢ P -∗ Q.
Proof. intros ->. apply wand_intro_r. by rewrite left_id. Qed.
(* A version that works with rewrite, in which bi_emp_valid is unfolded. *)
Lemma entails_wand' P Q : (P ⊢ Q) → emp ⊢ (P -∗ Q).
Proof. apply entails_wand. Qed.
Lemma wand_entails' P Q : (emp ⊢ (P -∗ Q)) → P ⊢ Q.
Proof. apply wand_entails. Qed.


Lemma entails_impl P Q : (P ⊢ Q) → (⊢ P → Q).
Proof. intros ->. apply impl_intro_l. auto. Qed.

Lemma and_parallel P1 P2 Q1 Q2 :
  (P1 ∧ P2) -∗ ((P1 -∗ Q1) ∧ (P2 -∗ Q2)) -∗ Q1 ∧ Q2.
Proof.
  apply wand_intro_r, and_intro.
  - rewrite !and_elim_l wand_elim_r. done.
  - rewrite !and_elim_r wand_elim_r. done.
Qed.

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


(* TODO: upstream? *)
Lemma impl_alt_eq P Q :
  (P → Q)%I ≡ (∃ (R : PROP), ⌜R ∧ P ⊢ Q⌝ ∧ R)%I.
Proof.
  apply equiv_entails ; split.
  - apply (exist_intro' _ _ (P → Q)%I).
    apply and_intro; last done.
    apply pure_intro. apply impl_elim_l.
  - apply exist_elim=>R. apply pure_elim_l=>HR.
    by apply impl_intro_r.
Qed.

End derived.

End bi.
