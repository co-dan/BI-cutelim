From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From iris_mod.bi Require Import bi.
From bunched Require Export syntax interp.

(** * Sequent calculus  *)
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
(* multiplicatives *)
| BI_Emp_R :
    empty ⊢ᴮ EMP
| BI_Emp_L C ϕ :
    (fill C empty ⊢ᴮ ϕ) →
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
    (fill C top ⊢ᴮ ϕ) →
    fill C (frml TOP) ⊢ᴮ ϕ
| BI_Conj_R Δ Δ' ϕ ψ :
    (Δ ⊢ᴮ ϕ) →
    (Δ' ⊢ᴮ ψ) →
    Δ ;, Δ' ⊢ᴮ CONJ ϕ ψ
| BI_Conj_L C ϕ ψ χ :
    (fill C (frml ϕ ;, frml ψ) ⊢ᴮ χ) →
    fill C (frml (CONJ ϕ ψ)) ⊢ᴮ χ
| BI_Impl_R Δ ϕ ψ :
    (Δ ;, frml ϕ ⊢ᴮ ψ) →
    Δ  ⊢ᴮ IMPL ϕ ψ
| BI_Impl_L C Δ ϕ ψ χ :
    (Δ ⊢ᴮ ϕ) →
    (fill C (frml ψ) ⊢ᴮ χ) →
    fill C (Δ ;, frml (IMPL ϕ ψ)) ⊢ᴮ χ
where "Δ ⊢ᴮ ϕ" := (proves Δ%B ϕ%B).

(** * Properties *)

(** Registering the right typeclasses for rewriting purposes. *)

Global Instance proves_proper : Proper ((≡) ==> (=) ==> (≡)) proves.
Proof.
  intros D1 D2 HD ϕ ? <-.
  split; intros H.
  - eapply BI_Equiv; eauto.
  - eapply BI_Equiv; [ symmetry | ]; eauto.
Qed.

Theorem seq_interp_sound {PROP : bi} (s : atom → PROP)
        Δ ϕ : (Δ ⊢ᴮ ϕ) → seq_interp PROP s Δ ϕ.
Proof.
  induction 1; unfold seq_interp; simpl; eauto; try rewrite -IHproves.
  all: try by apply bunch_interp_fill_mono.
  - by rewrite -H.
  - apply bunch_interp_fill_mono; simpl.
      by rewrite bi.and_elim_l.
  - apply bunch_interp_fill_mono; simpl.
    apply bi.and_intro; eauto.
  - by rewrite IHproves1 IHproves2.
  - by apply bi.wand_intro_r.
  - rewrite -IHproves2.
    apply bunch_interp_fill_mono; simpl.
    rewrite IHproves1. apply bi.wand_elim_r.
  - induction C as [|C Π IH]; simpl.
    { apply bi.False_elim. }
    rewrite -IH.
    destruct C; simpl; apply bunch_interp_fill_mono; simpl.
    all: by rewrite ?left_absorb ?right_absorb.
  - apply bi.True_intro.
  - by rewrite IHproves1 IHproves2.
  - by apply bi.impl_intro_r.
  - rewrite -IHproves2.
    apply bunch_interp_fill_mono; simpl.
    rewrite IHproves1. apply bi.impl_elim_r.
Qed.
