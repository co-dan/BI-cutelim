(* Bunches *)
From Coq Require Import ssreflect.
From stdpp Require Import prelude gmap fin_sets.
From bunched.algebra Require Import bi.

Declare Scope bunch_scope.
Delimit Scope bunch_scope with B.

(** * Generic syntax for bunches *)
Inductive sep := Comma | SemiC.

Inductive bunch {formula : Type} : Type :=
| frml (ϕ : formula)
| bnul (s : sep)
| bbin (s : sep) (Δ Γ : bunch)
.

(* Definition semic {frml} (Δ Γ : @bunch frml) := bbin SemiC Δ Γ. *)
(* Definition comma {frml} (Δ Γ : @bunch frml) := bbin Comma Δ Γ. *)
(* Definition top {frml} : @bunch frml := bnul SemiC. *)
(* Definition empty {frml} : @bunch frml := bnul Comma. *)

Notation "∅ₐ" := (bnul SemiC) : bunch_scope.
Notation "∅ₘ" := (bnul Comma) : bunch_scope.
Notation "Δ ';,' Γ" := (bbin SemiC Δ%B Γ%B) (at level 80, right associativity) : bunch_scope.
Notation "Δ ',,' Γ" := (bbin Comma Δ%B Γ%B) (at level 80, right associativity) : bunch_scope.

(** ** Bunched contexts with a hole *)
Inductive bunch_ctx_item {frml : Type} : Type :=
| CtxL (s : sep) (Δ2 : @bunch frml)
| CtxR (s : sep) (Δ1 : @bunch frml)
.

Definition CtxCommaL {frml} (Δ2 : bunch) : @bunch_ctx_item frml
  := CtxL Comma Δ2.
Definition CtxSemicL {frml} (Δ2 : bunch) : @bunch_ctx_item frml
  := CtxL SemiC Δ2.
Definition CtxCommaR {frml} (Δ1 : bunch) : @bunch_ctx_item frml
  := CtxR Comma Δ1.
Definition CtxSemicR {frml} (Δ1 : bunch) : @bunch_ctx_item frml
  := CtxR SemiC Δ1.

Definition bunch_ctx {frml} := list (@bunch_ctx_item frml).

Definition fill_item {frml} (F : @bunch_ctx_item frml) (Δ : bunch) : bunch :=
  match F with
  | CtxL s Δ2 => bbin s Δ Δ2
  | CtxR s Δ1 => bbin s Δ1 Δ
  end.

Definition fill {frml} (Π : @bunch_ctx frml) (Δ : bunch) : bunch :=
  foldl (flip fill_item) Δ Π.

#[global] Instance bunch_fmap : FMap (@bunch) :=
  fix go A B f Δ {struct Δ} := let _ : FMap (@bunch) := @go in
  match Δ with
  | bnul s => bnul s
  | bbin s Δ Δ' => bbin s (fmap f Δ) (fmap f Δ')
  | frml ϕ => frml (f ϕ)
  end%B.

Definition bunch_ctx_item_map {A B} (f : A → B) (F : @bunch_ctx_item A) :=
  match F with
  | CtxL s Δ => CtxL s (f <$> Δ)
  | CtxR s Δ => CtxR s (f <$> Δ)
  end.

Definition bunch_ctx_map {A B} (f : A → B) (Π : @bunch_ctx A) := map (bunch_ctx_item_map f) Π.


(** ** Bunch equivalence *)
(** Equivalence on bunches is defined to be the least congruence
      that satisfies the monoidal laws for (empty and comma) and (top
      and semicolon). *)
Inductive bunch_equiv_step {frml} : @bunch frml → @bunch frml → Prop :=
| BE_cong C Δ1 Δ2 : Δ1 =? Δ2 → fill C Δ1 =? fill C Δ2
| BE_unit_l s Δ : bbin s (bnul s) Δ =? Δ
| BE_comm s Δ1 Δ2 : bbin s Δ1 Δ2 =? bbin s Δ2 Δ1
| BE_assoc s Δ1 Δ2 Δ3 : bbin s Δ1 (bbin s Δ2 Δ3) =? bbin s (bbin s Δ1 Δ2) Δ3
where "Δ =? Γ" := (bunch_equiv_step Δ%B Γ%B).

Definition bunch_equiv {frml} := rtsc (@bunch_equiv_step frml).

(** Register [bunch_equiv] as [(≡)] *)
#[export] Instance equiv_bunch_equiv frml : Equiv (@bunch frml) := bunch_equiv.

(** * Properties *)

#[export] Instance equivalence_bunch_equiv frml : Equivalence ((≡@{@bunch frml})).
Proof. apply _. Qed.

#[export] Instance bbin_comm frml s : Comm (≡@{@bunch frml}) (bbin s).
Proof. intros X Y. apply rtsc_rl. apply BE_comm. Qed.
#[export] Instance bbin_assoc frml s : Assoc (≡@{@bunch frml}) (bbin s).
Proof. intros X Y Z. apply rtsc_lr. apply BE_assoc. Qed.
#[export] Instance bbin_leftid frml s : LeftId (≡@{@bunch frml}) (bnul s) (bbin s).
Proof. intros X. apply rtsc_lr. apply BE_unit_l. Qed.
#[export] Instance bbin_rightid frml s : RightId (≡@{@bunch frml}) (bnul s) (bbin s).
Proof. intros X. rewrite comm. apply rtsc_lr. apply BE_unit_l. Qed.

#[export] Instance fill_proper frml Π : Proper ((≡) ==> (≡@{@bunch frml})) (fill Π).
Proof.
  intros X Y.
  eapply rtc_congruence. clear X Y.
  intros X Y. apply sc_congruence. clear X Y.
  intros X Y ?. by econstructor.
Qed.

#[export] Instance bbin_proper frml s : Proper ((≡) ==> (≡) ==> (≡@{@bunch frml})) (bbin s).
Proof.
  intros Δ1 Δ2 H Δ1' Δ2' H'.
  change ((fill [CtxL s Δ1'] Δ1) ≡ (fill [CtxL s Δ2'] Δ2)).
  etrans.
  { eapply fill_proper; eauto. }
  simpl.
  change ((fill [CtxR s Δ2] Δ1') ≡ (fill [CtxR s Δ2] Δ2')).
  eapply fill_proper; eauto.
Qed.

Lemma fill_app {frml} (Π Π' : @bunch_ctx frml) (Δ : bunch) :
  fill (Π ++ Π') Δ = fill Π' (fill Π Δ).
Proof. by rewrite /fill foldl_app. Qed.

Lemma bunch_map_fill {A B} (f : A → B) Π Δ :
  f <$> (fill Π Δ) = fill (bunch_ctx_map f Π) (f <$> Δ).
Proof.
  revert Δ. induction Π as [|F Π IH] =>Δ/=//.
  rewrite IH. f_equiv. by destruct F; simpl.
Qed.

Lemma bunch_map_proper' {A B} (f : A → B) : Proper ((bunch_equiv_step) ==> (≡@{bunch})) (fmap f).
Proof.
  intros Δ1 Δ2 HD.
  induction HD; simpl.
  - rewrite !bunch_map_fill; by f_equiv.
  - by rewrite left_id.
  - by rewrite comm.
  - by rewrite assoc.
Qed.

#[global] Instance bunch_map_proper {A B} (f : A → B) : Proper ((≡) ==> (≡@{bunch})) (fmap f).
Proof.
  intros Δ1 Δ2 HD.
  induction HD as [|Δ1 Δ2 Δ3 HD1 HD]; first done.
  etrans; last by apply IHHD.
  destruct HD1 as [HD1 | HD1].
  - by apply bunch_map_proper'.
  - symmetry. by apply bunch_map_proper'.
Qed.

Section interp.
  Variable (PROP : bi).
  Context {formula : Type}.
  Notation bunch := (@bunch formula).
  Notation bunch_ctx := (@bunch_ctx formula).

  Implicit Types (A B C : PROP).
  Implicit Type Δ : bunch.
  Implicit Type Π : bunch_ctx.

  Variable (i : formula → PROP).

  Definition sep_interp (sp : sep) : PROP → PROP → PROP :=
    match sp with
    | Comma => (∗)
    | SemiC => (∧)
    end%I.
  #[export] Instance sep_interp_proper sp : Proper ((≡) ==> (≡) ==> (≡)) (sep_interp sp).
  Proof. destruct sp; apply _. Qed.
  #[export] Instance sep_interp_mono sp : Proper ((⊢) ==> (⊢) ==> (⊢)) (sep_interp sp).
  Proof. destruct sp; apply _. Qed.

  Fixpoint bunch_interp (Δ : bunch) : PROP :=
    match Δ with
    | frml ϕ => i ϕ
    | ∅ₐ => True
    | ∅ₘ => emp
    | bbin sp Δ Δ' => sep_interp sp (bunch_interp Δ) (bunch_interp Δ')
    end%B%I.

  Definition bunch_ctx_item_interp (F : bunch_ctx_item) : PROP → PROP :=
    λ P, match F with
        | CtxL sp Δ => sep_interp sp P (bunch_interp Δ)
        | CtxR sp Δ => sep_interp sp (bunch_interp Δ) P
        end%I.

  Definition bunch_ctx_interp Π : PROP → PROP :=
    λ P, foldl (flip bunch_ctx_item_interp) P Π.

  Lemma bunch_ctx_interp_cons F Π A :
    bunch_ctx_interp (F::Π) A = bunch_ctx_interp Π (bunch_ctx_item_interp F A).
  Proof. reflexivity. Qed.

  Global Instance bunch_ctx_interp_proper Π : Proper ((≡) ==> (≡)) (bunch_ctx_interp Π).
  Proof.
    induction Π as [|F Π]=>X Y HXY.
    - simpl; auto.
    - simpl.
      eapply IHΠ.
      destruct F; solve_proper.
  Qed.

  Lemma bunch_ctx_interp_decomp Π Δ :
    bunch_interp (fill Π Δ) ≡ bunch_ctx_interp Π (bunch_interp Δ).
  Proof.
    revert Δ. induction Π as [|C Π IH]=>Δ; first by reflexivity.
    apply bi.equiv_entails_2.
    - destruct C; simpl; by rewrite IH.
    - destruct C; simpl; by rewrite IH.
  Qed.

  Lemma bunch_interp_fill_item_mono (C : bunch_ctx_item) Δ Δ' :
    (bunch_interp Δ ⊢ bunch_interp Δ') →
    bunch_interp (fill_item C Δ) ⊢ bunch_interp (fill_item C Δ').
  Proof.
    intros H1.
    induction C as [ sp ? | sp ? ]; simpl; by rewrite H1.
  Qed.

  Lemma bunch_interp_fill_mono Π Δ Δ' :
    (bunch_interp Δ ⊢ bunch_interp Δ') →
    bunch_interp (fill Π Δ) ⊢ bunch_interp (fill Π Δ').
  Proof.
    revert Δ Δ'.
    induction Π as [|C Π IH]=> Δ Δ' H1; eauto.
    simpl. apply IH.
    by apply bunch_interp_fill_item_mono.
  Qed.

  Lemma bunch_ctx_interp_exist Π {I} (P : I → PROP) :
    bunch_ctx_interp Π (∃ (i : I), P i : PROP)%I ≡
                     (∃ i, bunch_ctx_interp Π (P i))%I.
  Proof.
    revert P. induction Π as [|F Π]=>P.
    { simpl. reflexivity. }
    rewrite bunch_ctx_interp_cons.
    Opaque bunch_ctx_interp.
    destruct F as [sp ?|sp ?]; destruct sp; simpl.
    + rewrite bi.sep_exist_r.
      apply (IHΠ (λ i, P i ∗ bunch_interp Δ2)%I).
    + rewrite bi.and_exist_r.
      apply (IHΠ (λ i, P i ∧ bunch_interp Δ2)%I).
    + rewrite bi.sep_exist_l.
      apply (IHΠ (λ i, bunch_interp Δ1 ∗ P i)%I).
    + rewrite bi.and_exist_l.
      apply (IHΠ (λ i, bunch_interp Δ1 ∧ P i)%I).
  Qed.

  Lemma bunch_interp_proper' : Proper ((bunch_equiv_step) ==> (≡)) bunch_interp.
  Proof.
    intros Δ1 Δ2. induction 1; eauto.
    - apply bi.equiv_entails_2.
      + apply bunch_interp_fill_mono; eauto.
        by apply bi.equiv_entails_1_1.
      + apply bunch_interp_fill_mono; eauto.
        by apply bi.equiv_entails_1_2.
    - simpl. destruct s; by rewrite left_id.
    - simpl. destruct s; by rewrite comm.
    - simpl. destruct s; by rewrite assoc.
  Qed.

  #[global] Instance bunch_interp_proper : Proper ((≡) ==> (≡)) bunch_interp.
  Proof.
    intros Δ1 Δ2. induction 1 as [|Δ1 Δ2 Δ3 HD1 HD]; first done.
    etrans; last by eassumption.
    destruct HD1; [| symmetry]; by apply bunch_interp_proper'.
  Qed.

  Global Instance bunch_ctx_interp_mono Π : Proper ((⊢) ==> (⊢)) (bunch_ctx_interp Π).
  Proof.
    induction Π as [|F Π]=>P1 P2 HP; first by simpl; auto.
    rewrite !bunch_ctx_interp_cons.
    apply IHΠ.
    destruct F as [[|] ? | [|] ?]; simpl; f_equiv; eauto.
  Qed.

  Lemma bunch_ctx_item_interp_pure F P Q :
    bunch_ctx_item_interp F (⌜P⌝ ∧ Q) ⊢ ⌜P⌝ ∧ bunch_ctx_item_interp F Q.
  Proof.
    destruct F as [[|] ? | [|] ?]; simpl.
    - rewrite bi.sep_and_r. f_equiv.
      apply bi.pure_sep_l.
    - by rewrite assoc.
    - rewrite bi.sep_and_l. f_equiv.
      rewrite comm.
      apply bi.pure_sep_l.
    - rewrite assoc. rewrite (comm _ _ ⌜P⌝%I).
      by rewrite assoc.
  Qed.

  Lemma bunch_ctx_interp_pure Π P Q :
    bunch_ctx_interp Π (⌜P⌝ ∧ Q) ⊢ ⌜P⌝ ∧ bunch_ctx_interp Π Q.
  Proof.
    revert Q. induction Π as [|F Π]=>Q; first by simpl; auto.
    rewrite !bunch_ctx_interp_cons.
    rewrite bunch_ctx_item_interp_pure.
    apply IHΠ.
  Qed.

End interp.

Arguments sep_interp {_} _ _ _.
Arguments bunch_interp {_ _} _ _.
Arguments bunch_ctx_interp {_ _} _ _ _.

