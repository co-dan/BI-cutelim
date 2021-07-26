From Coq Require Import ssreflect.
From stdpp Require Import prelude gmap fin_sets.
From iris_mod.bi Require Import bi.
From bunched Require Export syntax interp terms.

Module Type SIMPLE_STRUCT_EXT.
  Parameter rules : list (list (bterm nat) * bterm nat).
  Parameter rules_good : forall (Ts : list (bterm nat)) (T : bterm nat),
      (Ts, T) ∈ rules → linear_bterm T.
  (** A /simple structural rule/ is a rule of the form 

      Π(T₁[Δs]) ⊢ ϕ ... Π(Tₙ[Δs]) ⊢ ϕ
     ----------------------------------
           Π(T[Δs]) ⊢ ϕ

     where the T's are bunched terms (bunched contexts with variables).
     Furthermore, `T` (at the bottom) is _linear_: no varriable occurs
     more than once.

    We formalize a set of such rules as lists of `([T₁; ..; Tₙ], T)`.
*)

End SIMPLE_STRUCT_EXT.

(* When the set of rules is valid in the algebra *)
Definition rule_valid (PROP : bi) (Ts : list (bterm nat)) (T : bterm nat) :=
  ∀ (Xs : nat → PROP),
    bterm_alg_act T Xs ⊢
       ∃ Ti' : {Ti : bterm nat | Ti ∈ Ts }, bterm_alg_act (proj1_sig Ti') Xs.

(** * Sequent calculus  *)
Reserved Notation "P ⊢ᴮ Q" (at level 99, Q at level 200, right associativity).

Module Seqcalc (R : SIMPLE_STRUCT_EXT).
Import R.

Inductive proves : bunch → formula → Prop :=
(* structural *)
| BI_Axiom (a : atom) : frml (ATOM a) ⊢ᴮ ATOM a
| BI_Equiv Δ Δ' ϕ :
    (Δ ≡ Δ') → (Δ ⊢ᴮ ϕ) →
    Δ' ⊢ᴮ ϕ
| BI_Weaken Π Δ Δ' ϕ : (fill Π Δ ⊢ᴮ ϕ) →
                       fill Π (Δ ;, Δ') ⊢ᴮ ϕ
| BI_Contr Π Δ ϕ : (fill Π (Δ ;, Δ) ⊢ᴮ ϕ) →
                   fill Π Δ ⊢ᴮ ϕ
| BI_Simple_Ext Π (Δs : nat → bunch)
  (Ts : list (bterm nat)) (T : bterm nat) ϕ :
  (Ts, T) ∈ rules →
  (∀ Ti, Ti ∈ Ts → fill Π (bterm_ctx_act Ti Δs) ⊢ᴮ ϕ) →
  fill Π (bterm_ctx_act T Δs) ⊢ᴮ ϕ
(* multiplicatives *)
| BI_Emp_R :
    empty ⊢ᴮ EMP
| BI_Emp_L Π ϕ :
    (fill Π empty ⊢ᴮ ϕ) →
    fill Π (frml EMP) ⊢ᴮ ϕ
| BI_Sep_R Δ Δ' ϕ ψ :
    (Δ ⊢ᴮ ϕ) →
    (Δ' ⊢ᴮ ψ) →
    Δ ,, Δ' ⊢ᴮ SEP ϕ ψ
| BI_Sep_L Π ϕ ψ χ :
    (fill Π (frml ϕ ,, frml ψ) ⊢ᴮ χ) →
    fill Π (frml (SEP ϕ ψ)) ⊢ᴮ χ
| BI_Wand_R Δ ϕ ψ :
    (Δ ,, frml ϕ ⊢ᴮ ψ) →
    Δ  ⊢ᴮ WAND ϕ ψ
| BI_Wand_L Π Δ ϕ ψ χ :
    (Δ ⊢ᴮ ϕ) →
    (fill Π (frml ψ) ⊢ᴮ χ) →
    fill Π (Δ ,, frml (WAND ϕ ψ)) ⊢ᴮ χ
(* additives *)
| BI_False_L Π ϕ :
    fill Π (frml BOT) ⊢ᴮ ϕ
| BI_True_R Δ :
    Δ ⊢ᴮ TOP
| BI_True_L Π ϕ :
    (fill Π top ⊢ᴮ ϕ) →
    fill Π (frml TOP) ⊢ᴮ ϕ
| BI_Conj_R Δ Δ' ϕ ψ :
    (Δ ⊢ᴮ ϕ) →
    (Δ' ⊢ᴮ ψ) →
    Δ ;, Δ' ⊢ᴮ CONJ ϕ ψ
| BI_Conj_L Π ϕ ψ χ :
    (fill Π (frml ϕ ;, frml ψ) ⊢ᴮ χ) →
    fill Π (frml (CONJ ϕ ψ)) ⊢ᴮ χ
| BI_Impl_R Δ ϕ ψ :
    (Δ ;, frml ϕ ⊢ᴮ ψ) →
    Δ  ⊢ᴮ IMPL ϕ ψ
| BI_Impl_L Π Δ ϕ ψ χ :
    (Δ ⊢ᴮ ϕ) →
    (fill Π (frml ψ) ⊢ᴮ χ) →
    fill Π (Δ ;, frml (IMPL ϕ ψ)) ⊢ᴮ χ
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

Lemma collapse_l (Π : bunch_ctx) (Δ : bunch) (ϕ : formula) :
    (fill Π Δ ⊢ᴮ ϕ) → fill Π (frml (collapse Δ)) ⊢ᴮ ϕ.
Proof.
  revert Π. induction Δ=>Π; simpl; eauto.
  - intros HX.
    by apply BI_True_L, HX.
  - intros HX.
    by apply BI_Emp_L, HX.
  - intros HX.
    apply BI_Sep_L.
    apply (IHΔ1 (CtxCommaL _::Π)); simpl.
    apply (IHΔ2 (CtxCommaR _::Π)); simpl.
    apply HX.
  - intros HX.
    apply BI_Conj_L.
    apply (IHΔ1 (CtxSemicL _::Π)); simpl.
    apply (IHΔ2 (CtxSemicR _::Π)); simpl.
    apply HX.
Qed.

Theorem seq_interp_sound {PROP : bi} (s : atom → PROP) Δ ϕ :
  (∀ Ts T, (Ts, T) ∈ rules → rule_valid PROP Ts T) →
  (Δ ⊢ᴮ ϕ) →
  seq_interp PROP s Δ ϕ.
Proof.
  intros Hrules.
  induction 1; unfold seq_interp; simpl; eauto; try rewrite -IHproves.
  all: try by apply bunch_interp_fill_mono.
  - by rewrite -H.
  - apply bunch_interp_fill_mono; simpl.
      by rewrite bi.and_elim_l.
  - apply bunch_interp_fill_mono; simpl.
    apply bi.and_intro; eauto.
  - assert (rule_valid PROP Ts T) as HH.
    { eapply Hrules; auto. }
    specialize (HH (bunch_interp _ s ∘ Δs)).
    rewrite bunch_ctx_interp_decomp.
    rewrite bterm_ctx_alg_act.
    rewrite HH.
    rewrite bunch_ctx_interp_exist.
    apply bi.exist_elim=>Ti'.
    destruct Ti' as [Ti HTi].
    rewrite -bterm_ctx_alg_act.
    rewrite -bunch_ctx_interp_decomp.
    by apply H1.
  - by rewrite IHproves1 IHproves2.
  - by apply bi.wand_intro_r.
  - rewrite -IHproves2.
    apply bunch_interp_fill_mono; simpl.
    rewrite IHproves1. apply bi.wand_elim_r.
  - induction Π as [|C Π IH]; simpl.
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

End Seqcalc.
