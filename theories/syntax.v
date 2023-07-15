(* Formulas, bunches *)
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


(** ** Bunch equivalence *)
(** Equivalence on bunches is defined to be the least congruence
      that satisfies the monoidal laws for (empty and comma) and (top
      and semicolon). *)
Inductive bunch_equiv {frml} : @bunch frml → @bunch frml → Prop :=
| BE_refl Δ : Δ =? Δ
| BE_sym Δ1 Δ2 : Δ1 =? Δ2 → Δ2 =? Δ1
| BE_trans Δ1 Δ2 Δ3 : Δ1 =? Δ2 → Δ2 =? Δ3 → Δ1 =? Δ3
| BE_cong C Δ1 Δ2 : Δ1 =? Δ2 → fill C Δ1 =? fill C Δ2
| BE_unit_l s Δ : bbin s (bnul s) Δ =? Δ
| BE_comm s Δ1 Δ2 : bbin s Δ1 Δ2 =? bbin s Δ2 Δ1
| BE_assoc s Δ1 Δ2 Δ3 : bbin s Δ1 (bbin s Δ2 Δ3) =? bbin s (bbin s Δ1 Δ2) Δ3
where "Δ =? Γ" := (bunch_equiv Δ%B Γ%B).

(** Register [bunch_equiv] as [(≡)] *)
#[export] Instance equiv_bunch_equiv frml : Equiv (@bunch frml) := bunch_equiv.

(** * Properties *)

#[export] Instance equivalence_bunch_equiv frml : Equivalence ((≡@{@bunch frml})).
Proof.
  repeat split.
  - intro x. econstructor.
  - intros x y Hxy. by econstructor.
  - intros x y z Hxy Hyz. by econstructor.
Qed.

#[export] Instance bbin_comm frml s : Comm (≡@{@bunch frml}) (bbin s).
Proof. intros X Y. apply BE_comm. Qed.
#[export] Instance bbin_assoc frml s : Assoc (≡@{@bunch frml}) (bbin s).
Proof. intros X Y Z. apply BE_assoc. Qed.
#[export] Instance bbin_leftid frml s : LeftId (≡@{@bunch frml}) (bnul s) (bbin s).
Proof. intros X. apply BE_unit_l. Qed.
#[export] Instance bbin_rightid frml s : RightId (≡@{@bunch frml}) (bnul s) (bbin s).
Proof. intros X. rewrite comm. apply BE_unit_l. Qed.

#[export] Instance fill_proper frml Π : Proper ((≡) ==> (≡@{@bunch frml})) (fill Π).
Proof. intros X Y. apply BE_cong. Qed.

#[export] Instance bbin_proper frml s : Proper ((≡) ==> (≡) ==> (≡@{@bunch frml})) (bbin s).
Proof.
  intros Δ1 Δ2 H Δ1' Δ2' H'.
  change ((fill [CtxL s Δ1'] Δ1) ≡ (fill [CtxL s Δ2'] Δ2)).
  etrans.
  { eapply BE_cong; eauto. }
  simpl.
  change ((fill [CtxR s Δ2] Δ1') ≡ (fill [CtxR s Δ2] Δ2')).
  eapply BE_cong; eauto.
Qed.

Lemma fill_app {frml} (Π Π' : @bunch_ctx frml) (Δ : bunch) :
  fill (Π ++ Π') Δ = fill Π' (fill Π Δ).
Proof. by rewrite /fill foldl_app. Qed.


(** * Formulas *)
Definition atom := nat.

Inductive formula : Type :=
| TOP
| EMP
| BOT
| ATOM (A : atom)
| CONJ (ϕ ψ : formula)
| DISJ (ϕ ψ : formula)
| SEP (ϕ ψ : formula)
| IMPL (ϕ ψ : formula)
| WAND (ϕ ψ : formula)
.

(** "Collapse" internalizes the bunch as a formula. *)
Fixpoint collapse (Δ : @bunch formula) : formula :=
  match Δ with
  | frml ϕ => ϕ
  | ∅ₐ => TOP
  | ∅ₘ => EMP
  | Δ ,, Δ' => SEP (collapse Δ) (collapse Δ')
  | Δ ;, Δ' => CONJ (collapse Δ) (collapse Δ')
  end%B.

Inductive collapse_gr : @bunch formula → formula → Prop :=
| collapse_frml ϕ : collapse_gr (frml ϕ) ϕ
| collapse_top : collapse_gr ∅ₐ%B TOP
| collapse_emp : collapse_gr ∅ₘ%B EMP
| collapse_sep Δ1 Δ2 ϕ1 ϕ2 :
  collapse_gr Δ1 ϕ1 →
  collapse_gr Δ2 ϕ2 →
  collapse_gr (Δ1 ,, Δ2)%B (SEP ϕ1 ϕ2)
| collapse_conj Δ1 Δ2 ϕ1 ϕ2 :
  collapse_gr Δ1 ϕ1 →
  collapse_gr Δ2 ϕ2 →
  collapse_gr (Δ1 ;, Δ2)%B (CONJ ϕ1 ϕ2)
.

Lemma collapse_gr_sound Δ : collapse_gr Δ (collapse Δ).
Proof. induction Δ; simpl; try destruct s; try by econstructor. Qed.

Lemma collapse_gr_complete Δ ϕ : collapse_gr Δ ϕ → collapse Δ = ϕ.
Proof. induction 1; simpl; subst; eauto. Qed.
