(** BI + □ *)
From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From bunched.algebra Require Import bi.
From bunched Require Export bunches bunch_decomp.
From bunched.s4 Require Import formula.

Declare Scope bunch_scope.
Delimit Scope bunch_scope with B.

(** ** Sequent calculus itself *)
Reserved Notation "P ⊢ᴮ Q" (at level 99, Q at level 200, right associativity).
Inductive proves : bunch → formula → Prop :=
(* structural *)
| BI_Axiom (a : atom) : frml (ATOM a) ⊢ᴮ ATOM a
| BI_Equiv Δ Δ' ϕ :
    (Δ ≡ Δ') → (Δ ⊢ᴮ ϕ) →
    Δ' ⊢ᴮ ϕ
| BI_Weaken C Δ Δ' ϕ : (fill C Δ ⊢ᴮ ϕ) →
                       fill C (Δ ;, Δ') ⊢ᴮ ϕ
| BI_Contr C Δ ϕ : (fill C (Δ ;, Δ) ⊢ᴮ ϕ) →
                   fill C Δ ⊢ᴮ ϕ
(* modalities *)
| BI_Box_L Π ϕ ψ :
    (fill Π (frml ϕ) ⊢ᴮ ψ) →
    fill Π (frml (BOX ϕ)) ⊢ᴮ ψ
| BI_Box_R Δ ϕ :
    (BOX <$> Δ ⊢ᴮ ϕ) →
    BOX <$> Δ ⊢ᴮ BOX ϕ
(* multiplicatives *)
| BI_Emp_R :
    ∅ₘ ⊢ᴮ EMP
| BI_Emp_L C ϕ :
    (fill C ∅ₘ ⊢ᴮ ϕ) →
    fill C (frml EMP) ⊢ᴮ ϕ
| BI_Sep_R Δ Δ' ϕ ψ :
    (Δ ⊢ᴮ ϕ) →
    (Δ' ⊢ᴮ ψ) →
    Δ ,, Δ' ⊢ᴮ SEP ϕ ψ
| BI_Sep_L C ϕ ψ χ :
    (fill C (frml ϕ ,, frml ψ) ⊢ᴮ χ) →
    fill C (frml (SEP ϕ ψ)) ⊢ᴮ χ
| BI_Wand_R Δ ϕ ψ :
    (Δ ,, frml ϕ ⊢ᴮ ψ) →
    Δ  ⊢ᴮ WAND ϕ ψ
| BI_Wand_L C Δ ϕ ψ χ :
    (Δ ⊢ᴮ ϕ) →
    (fill C (frml ψ) ⊢ᴮ χ) →
    fill C (Δ ,, frml (WAND ϕ ψ)) ⊢ᴮ χ
(* additives *)
| BI_False_L C ϕ :
    fill C (frml BOT) ⊢ᴮ ϕ
| BI_True_R Δ :
    Δ ⊢ᴮ TOP
| BI_True_L C ϕ :
    (fill C ∅ₐ ⊢ᴮ ϕ) →
    fill C (frml TOP) ⊢ᴮ ϕ
| BI_Conj_R Δ Δ' ϕ ψ :
    (Δ ⊢ᴮ ϕ) →
    (Δ' ⊢ᴮ ψ) →
    Δ ;, Δ' ⊢ᴮ CONJ ϕ ψ
| BI_Conj_L C ϕ ψ χ :
    (fill C (frml ϕ ;, frml ψ) ⊢ᴮ χ) →
    fill C (frml (CONJ ϕ ψ)) ⊢ᴮ χ
| BI_Disj_R1 Δ ϕ ψ :
    (Δ ⊢ᴮ ϕ) →
    Δ ⊢ᴮ DISJ ϕ ψ
| BI_Disj_R2 Δ ϕ ψ :
    (Δ ⊢ᴮ ψ) →
    Δ ⊢ᴮ DISJ ϕ ψ
| BI_Disj_L Π ϕ ψ χ :
    (fill Π (frml ϕ) ⊢ᴮ χ) →
    (fill Π (frml ψ) ⊢ᴮ χ) →
    fill Π (frml (DISJ ϕ ψ)) ⊢ᴮ χ
| BI_Impl_R Δ ϕ ψ :
    (Δ ;, frml ϕ ⊢ᴮ ψ) →
    Δ  ⊢ᴮ IMPL ϕ ψ
| BI_Impl_L C Δ ϕ ψ χ :
    (Δ ⊢ᴮ ϕ) →
    (fill C (frml ψ) ⊢ᴮ χ) →
    fill C (Δ ;, frml (IMPL ϕ ψ)) ⊢ᴮ χ
where "Δ ⊢ᴮ ϕ" := (proves Δ%B ϕ%B).


Global Instance proves_proper : Proper ((≡) ==> (=) ==> (≡)) proves.
Proof.
  intros D1 D2 HD ϕ ? <-.
  split; intros H.
  - eapply BI_Equiv; eauto.
  - eapply BI_Equiv; [ symmetry | ]; eauto.
Qed.

(** Additional lemmas for bunch_decompose and box *)
Lemma bunch_decomp_box_frml Π ϕ Δ :
  bunch_decomp (BOX <$> Δ) Π (frml ϕ) → ∃ ψ, ϕ = BOX ψ.
Proof.
  revert Π. induction Δ=>/= Π H1; try by inversion H1.
  - inversion H1; simplify_eq/=. naive_solver.
  - inversion H1 as [Δ|sp Δ1' Δ2' Π' Δ H1' |sp Δ1' Δ2' Π' Δ H1']; simplify_eq/=.
    + eapply IHΔ1; eauto.
    + eapply IHΔ2; eauto.
Qed.

Lemma bunch_decomp_box Δ Π ϕ :
  bunch_decomp (BOX <$> Δ) Π (frml (BOX ϕ)) →
  ∃ Π', Π = bunch_ctx_map BOX Π' ∧ bunch_decomp Δ Π' (frml ϕ).
Proof.
  revert Π. induction Δ=>/= Π H1; try by inversion H1.
  - inversion H1. simplify_eq/=. exists []. split; eauto.
    econstructor.
  - inversion H1 as [Δ|sp Δ1' Δ2' Π' Δ H1' |sp Δ1' Δ2' Π' Δ H1']; simplify_eq/=.
    + destruct (IHΔ1 _ H1') as (Π'1 & -> & Hdec).
      exists (Π'1 ++ [CtxL s Δ2]).
      rewrite /bunch_ctx_map map_app /=. split; auto.
        by econstructor.
    + destruct (IHΔ2 _ H1') as (Π'1 & -> & Hdec).
      exists (Π'1 ++ [CtxR s Δ1]).
      rewrite /bunch_ctx_map map_app /=. split; auto.
        by econstructor.
Qed.

(** Some convenient derived rules *)
Lemma BI_Boxes_L Π Δ ϕ :
  (fill Π Δ ⊢ᴮ ϕ) →
  (fill Π (BOX <$> Δ) ⊢ᴮ ϕ).
Proof.
  revert Π. induction Δ=> Π IH /=; eauto.
  - by apply BI_Box_L.
  - apply (IHΔ1 ((CtxL s (fmap BOX Δ2))::Π)). simpl.
    apply (IHΔ2 ((CtxR s Δ1)::Π)). done.
Qed.

Lemma BI_Collapse_L Π Δ ϕ :
  (fill Π Δ ⊢ᴮ ϕ) →
  (fill Π (frml (collapse Δ)) ⊢ᴮ ϕ).
Proof.
  revert Π. induction Δ=>Π; simpl; eauto.
  - intros HX.
    destruct s.
    + by apply BI_Emp_L, HX.
    + by apply BI_True_L, HX.
  - intros HX.
    destruct s.
    + apply BI_Sep_L.
      apply (IHΔ1 (CtxCommaL _::Π)); simpl.
      apply (IHΔ2 (CtxCommaR _::Π)); simpl.
      apply HX.
    + apply BI_Conj_L.
      apply (IHΔ1 (CtxSemicL _::Π)); simpl.
      apply (IHΔ2 (CtxSemicR _::Π)); simpl.
      apply HX.
Qed.
