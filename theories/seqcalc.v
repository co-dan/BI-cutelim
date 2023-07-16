(** Sequent calculus for BI, parameterized by a set of structural rules. *)
From Coq Require Import ssreflect.
From stdpp Require Import prelude gmap fin_sets.
From bunched.algebra Require Import bi.
From bunched Require Export bunches formula terms interp.

Module Type ANALYTIC_STRUCT_EXT.
(** An _analytic structural rule_ is a rule of the form

<<
      Π(T₁[Δs]) ⊢ ϕ    ...    Π(T[Δs]) ⊢ ϕ
     -----------------------------------------
                  Π(T[Δs]) ⊢ ϕ
>>

     where the T's are bunched terms (bunches built out of commas,
     semicolons, and variables). Furthermore, <<T>> (at the bottom)
     is _linear_: no varriable occurs more than once.

     We formalize a set of such rules as lists of tuples :
        <<([T₁; ..; T], T)>>.

     Every structural rule can be turned into an equivalent analytic rule.
     See the modules <<terms.v>> and <<analytic_completion.v>> for the details.
*)

  Definition bterm := bterm nat.
  Parameter rules : list structural_rule.
  Parameter rules_good : ∀ s, s ∈ rules → is_analytical s.

End ANALYTIC_STRUCT_EXT.

(** * Sequent calculus *)
Reserved Notation "P ⊢ᴮ Q" (at level 99, Q at level 200, right associativity).

(** ... parameterized over an arbitrary collection of simple structural rules. *)
Module Seqcalc (R : ANALYTIC_STRUCT_EXT).
Import R.

Notation bunch := (@bunch formula).
Notation bunch_ctx := (@bunch_ctx formula).

Inductive proves : bunch → formula → Prop :=
(** Structural rules: *)
| BI_Axiom (a : atom) : frml (ATOM a) ⊢ᴮ ATOM a
| BI_Equiv Δ Δ' ϕ :
    (Δ ≡ Δ') → (Δ ⊢ᴮ ϕ) →
    Δ' ⊢ᴮ ϕ
| BI_Weaken Π Δ Δ' ϕ : (fill Π Δ ⊢ᴮ ϕ) →
                       fill Π (Δ ;, Δ') ⊢ᴮ ϕ
| BI_Contr Π Δ ϕ : (fill Π (Δ ;, Δ) ⊢ᴮ ϕ) →
                   fill Π Δ ⊢ᴮ ϕ
| BI_Simple_Ext Π (Δs : nat → bunch)
  (Ts : list bterm) (T : bterm) ϕ :
  (Ts, T) ∈ rules →
  (∀ Ti, Ti ∈ Ts → fill Π (bterm_ctx_act Ti Δs) ⊢ᴮ ϕ) →
  fill Π (bterm_ctx_act T Δs) ⊢ᴮ ϕ
(** Multiplicatives: *)
| BI_Emp_R :
    ∅ₘ ⊢ᴮ EMP
| BI_Emp_L Π ϕ :
    (fill Π ∅ₘ ⊢ᴮ ϕ) →
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
(** Additives: *)
| BI_False_L Π ϕ :
    fill Π (frml BOT) ⊢ᴮ ϕ
| BI_True_R Δ :
    Δ ⊢ᴮ TOP
| BI_True_L Π ϕ :
    (fill Π ∅ₐ ⊢ᴮ ϕ) →
    fill Π (frml TOP) ⊢ᴮ ϕ
| BI_Conj_R Δ Δ' ϕ ψ :
    (Δ ⊢ᴮ ϕ) →
    (Δ' ⊢ᴮ ψ) →
    Δ ;, Δ' ⊢ᴮ CONJ ϕ ψ
| BI_Conj_L Π ϕ ψ χ :
    (fill Π (frml ϕ ;, frml ψ) ⊢ᴮ χ) →
    fill Π (frml (CONJ ϕ ψ)) ⊢ᴮ χ
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

(** Identity expansion *)
Lemma seqcalc_id_ext ϕ : frml ϕ ⊢ᴮ ϕ.
Proof.
  induction ϕ.
  - by econstructor.
  - eapply (BI_Emp_L []). by econstructor.
  - by eapply (BI_False_L []).
  - by econstructor.
  - eapply (BI_Conj_L []). eapply (BI_Conj_R); by econstructor.
  - eapply (BI_Disj_L []).
    + by econstructor; eapply IHϕ1.
    + by econstructor; eapply IHϕ2.
  - eapply (BI_Sep_L []). eapply (BI_Sep_R); by econstructor.
  - eapply BI_Impl_R. rewrite comm. eapply (BI_Impl_L []); eauto.
  - eapply BI_Wand_R. rewrite comm. eapply (BI_Wand_L []); eauto.
Qed.

(** "Collapsing" a bunch as a derived left rule *)
Lemma BI_Collapse_L (Π : bunch_ctx) (Δ : bunch) (ϕ : formula) :
    (fill Π Δ ⊢ᴮ ϕ) → fill Π (frml (collapse Δ)) ⊢ᴮ ϕ.
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

(** * Interpretation *)
(** Associated with the set of rules:
     when is the set of rules is valid in an algebra? *)
Definition rule_valid (PROP : bi) (Ts : list bterm) (T : bterm) :=
  ∀ (Xs : nat → PROP),
    bterm_alg_act T Xs ⊢
       ∃ Ti' : {Ti : bterm | Ti ∈ Ts }, bterm_alg_act (proj1_sig Ti') Xs.

(** Sequent calculus is sound w.r.t. the BI algebras. *)
Theorem seq_interp_sound {PROP : bi} (s : atom → PROP) Δ ϕ :
  (∀ Ts T, (Ts, T) ∈ rules → rule_valid PROP Ts T) →
  (Δ ⊢ᴮ ϕ) →
  seq_interp s Δ ϕ.
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
    specialize (HH (bunch_interp (formula_interp s) ∘ Δs)).
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
    destruct C as [[]?|[]?]; simpl; apply bunch_interp_fill_mono; simpl.
    all: by rewrite ?left_absorb ?right_absorb.
  - apply bi.True_intro.
  - by rewrite IHproves1 IHproves2.
  - by apply bi.or_intro_l.
  - by apply bi.or_intro_r.
  - rewrite bunch_ctx_interp_decomp. simpl.
    trans (bunch_ctx_interp PROP (formula_interp s) Π (∃ (x : bool), if x then bunch_interp (formula_interp s) (frml ϕ) else bunch_interp (formula_interp s) (frml ψ))).
    { apply bunch_ctx_interp_mono.
      apply bi.or_elim.
      - by eapply (bi.exist_intro' _ _ true).
      - by eapply (bi.exist_intro' _ _ false). }
    rewrite bunch_ctx_interp_exist.
    apply bi.exist_elim.
    intros [|];  rewrite <- bunch_ctx_interp_decomp.
    + eapply IHproves1.
    + eapply IHproves2.
  - by apply bi.impl_intro_r.
  - rewrite -IHproves2.
    apply bunch_interp_fill_mono; simpl.
    rewrite IHproves1. apply bi.impl_elim_r.
Qed.


End Seqcalc.
