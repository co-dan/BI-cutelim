(* Formulas, bunches *)
From Coq Require Import ssreflect.
From stdpp Require Import prelude gmap fin_sets.
From iris_mod.bi Require Import bi.

Declare Scope bunch_scope.
Delimit Scope bunch_scope with B.

(** * Formulas and bunches *)
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

Inductive bunch : Type :=
| frml (ϕ : formula)
| top : bunch
| empty : bunch
| comma (Δ1 Δ2 : bunch)
| semic (Δ1 Δ2 : bunch)
.

Notation "Δ ';,' Γ" := (semic Δ%B Γ%B) (at level 80, right associativity) : bunch_scope.
Notation "Δ ',,' Γ" := (comma Δ%B Γ%B) (at level 80, right associativity) : bunch_scope.

(** ** Bunched contexts with a hole *)
Inductive bunch_ctx_item : Type :=
| CtxCommaL (Δ2 : bunch)    (* Δ ↦ Δ , Δ2 *)
| CtxCommaR (Δ1 : bunch)    (* Δ ↦ Δ1, Δ *)
| CtxSemicL (Δ2 : bunch)    (* Δ ↦ Δ; Δ2 *)
| CtxSemicR (Δ1 : bunch)    (* Δ ↦ Δ1; Δ *)
.

Definition bunch_ctx := list bunch_ctx_item.

Definition fill_item (F : bunch_ctx_item) (Δ : bunch) : bunch :=
  match F with
  | CtxCommaL Δ2 => Δ ,, Δ2
  | CtxCommaR Δ1 => Δ1 ,, Δ
  | CtxSemicL Δ2 => Δ ;, Δ2
  | CtxSemicR Δ1 => Δ1 ;, Δ
  end%B.

Definition fill (Π : bunch_ctx) (Δ : bunch) : bunch :=
  foldl (flip fill_item) Δ Π.

(** "Collapse" internalizes the bunch as a formula. *)
Fixpoint collapse (Δ : bunch) : formula :=
  match Δ with
  | top => TOP
  | empty => EMP
  | frml ϕ => ϕ
  | (Δ ,, Δ')%B => SEP (collapse Δ) (collapse Δ')
  | (Δ ;, Δ')%B => CONJ (collapse Δ) (collapse Δ')
  end.

(** ** Bunch equivalence *)
(** Equivalence on bunches is defined to be the least congruence
      that satisfies the monoidal laws for (empty and comma) and (top
      and semicolon). *)
Inductive bunch_equiv : bunch → bunch → Prop :=
| BE_refl Δ : Δ =? Δ
| BE_sym Δ1 Δ2 : Δ1 =? Δ2 → Δ2 =? Δ1
| BE_trans Δ1 Δ2 Δ3 : Δ1 =? Δ2 → Δ2 =? Δ3 → Δ1 =? Δ3
| BE_cong C Δ1 Δ2 : Δ1 =? Δ2 → fill C Δ1 =? fill C Δ2
| BE_comma_unit_l Δ : (empty ,, Δ)%B =? Δ
| BE_comma_comm Δ1 Δ2  : (Δ1 ,, Δ2)%B =? (Δ2 ,, Δ1)%B
| BE_comma_assoc Δ1 Δ2 Δ3  : (Δ1 ,, (Δ2 ,, Δ3))%B =? ((Δ1 ,, Δ2) ,, Δ3)%B
| BE_semic_unit_l Δ : (top ;, Δ)%B =? Δ
| BE_semic_comm Δ1 Δ2  : (Δ1 ;, Δ2)%B =? (Δ2 ;, Δ1)%B
| BE_semic_assoc Δ1 Δ2 Δ3  : (Δ1 ;, (Δ2 ;, Δ3))%B =? ((Δ1 ;, Δ2) ;, Δ3)%B
where "Δ =? Γ" := (bunch_equiv Δ%B Γ%B).

(** Register [bunch_equiv] as [(≡)] *)
Global Instance equiv_bunch_equiv : Equiv bunch := bunch_equiv.

(** * Properties *)

Global Instance equivalence_bunch_equiv : Equivalence ((≡@{bunch})).
Proof.
  repeat split.
  - intro x. econstructor.
  - intros x y Hxy. by econstructor.
  - intros x y z Hxy Hyz. by econstructor.
Qed.

Global Instance comma_comm : Comm (≡) comma.
Proof. intros X Y. apply BE_comma_comm. Qed.
Global Instance semic_comm : Comm (≡) semic.
Proof. intros X Y. apply BE_semic_comm. Qed.
Global Instance comma_assoc : Assoc (≡) comma.
Proof. intros X Y Z. apply BE_comma_assoc. Qed.
Global Instance semic_assoc : Assoc (≡) semic.
Proof. intros X Y Z. apply BE_semic_assoc. Qed.
Global Instance comma_left_id : LeftId (≡) empty comma.
Proof. intros X. by econstructor. Qed.
Global Instance comma_right_id : RightId (≡) empty comma.
Proof. intros X. rewrite comm. by econstructor. Qed.
Global Instance semic_left_id : LeftId (≡) top semic.
Proof. intros X. by econstructor. Qed.
Global Instance semic_right_id : RightId (≡) top semic.
Proof. intros X. rewrite comm. by econstructor. Qed.

Global Instance fill_proper Π : Proper ((≡) ==> (≡)) (fill Π).
Proof. intros X Y. apply BE_cong. Qed.

Global Instance comma_proper : Proper ((≡) ==> (≡) ==> (≡)) comma.
Proof.
  intros Δ1 Δ2 H Δ1' Δ2' H'.
  change ((fill [CtxCommaL Δ1'] Δ1) ≡ (fill [CtxCommaL Δ2'] Δ2)).
  etrans.
  { eapply BE_cong; eauto. }
  simpl.
  change ((fill [CtxCommaR Δ2] Δ1') ≡ (fill [CtxCommaR Δ2] Δ2')).
  eapply BE_cong; eauto.
Qed.

Global Instance semic_proper : Proper ((≡) ==> (≡) ==> (≡)) semic.
Proof.
  intros Δ1 Δ2 H Δ1' Δ2' H'.
  change ((fill [CtxSemicL Δ1'] Δ1) ≡ (fill [CtxSemicL Δ2'] Δ2)).
  etrans.
  { eapply BE_cong; eauto. }
  simpl.
  change ((fill [CtxSemicR Δ2] Δ1') ≡ (fill [CtxSemicR Δ2] Δ2')).
  eapply BE_cong; eauto.
Qed.

Lemma fill_app (Π Π' : bunch_ctx) (Δ : bunch) :
  fill (Π ++ Π') Δ = fill Π' (fill Π Δ).
Proof. by rewrite /fill foldl_app. Qed.

