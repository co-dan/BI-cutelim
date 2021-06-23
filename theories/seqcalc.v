From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From iris_mod.bi Require Import bi.

Declare Scope bunch_scope.
Delimit Scope bunch_scope with B.

(** * Syntax and sequence calculus for BI *)

Definition atom := nat.

(** ** Formulas and bunches *)
Inductive formula : Type :=
| TOP
| EMP
| BOT
| ATOM (A : atom)
| CONJ (ϕ ψ : formula)
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

Local Infix ";," := semic (at level 80, right associativity) : bunch_scope.
Local Infix ",," := comma (at level 80, right associativity) : bunch_scope.

(** "Collapse" internalizes the bunch as a formula. *)
Fixpoint collapse (Δ : bunch) : formula :=
  match Δ with
  | top => TOP
  | empty => EMP
  | frml ϕ => ϕ
  | (Δ ,, Δ')%B => SEP (collapse Δ) (collapse Δ')
  | (Δ ;, Δ')%B => CONJ (collapse Δ) (collapse Δ')
  end.

(** Bunched contexts with a hole *)
Inductive bunch_ctx_item : Type :=
| CtxCommaL (Δ2 : bunch)    (* Δ ↦ Δ , Δ2 *)
| CtxCommaR (Δ1 : bunch)    (* Δ ↦ Δ1, Δ *)
| CtxSemicL (Δ2 : bunch)    (* Δ ↦ Δ; Δ2 *)
| CtxSemicR (Δ1 : bunch)    (* Δ ↦ Δ1; Δ *)
.

Definition bunch_ctx := list bunch_ctx_item.

Definition fill_item (C : bunch_ctx_item) (Δ : bunch) : bunch :=
  match C with
  | CtxCommaL Δ2 => Δ ,, Δ2
  | CtxCommaR Δ1 => Δ1 ,, Δ
  | CtxSemicL Δ2 => Δ ;, Δ2
  | CtxSemicR Δ1 => Δ1 ;, Δ
  end%B.

Definition fill (Π : bunch_ctx) (Δ : bunch) : bunch :=
  foldl (flip fill_item) Δ Π.

(** ** Bunch equivalence *)
(** Equivalence on bunches is defined to be the least congruence
      that satisfies the monoidal laws for (empty and comma) and (top
      and semicolon). *)
Inductive bunch_equiv : bunch → bunch → Type :=
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

(** ** Sequent calculus itself *)
Reserved Notation "P ⊢ᴮ Q" (at level 99, Q at level 200, right associativity).
Inductive proves : bunch → formula → Type :=
(* structural *)
| BI_Axiom (a : atom) : frml (ATOM a) ⊢ᴮ ATOM a
| BI_Equiv Δ Δ' ϕ :
    (Δ =? Δ') → (Δ ⊢ᴮ ϕ) →
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


Ltac reshape_bunch Δ tac :=
  let rec go K Δ :=
    match Δ with
    | _                               => tac K Δ
    | (?Δ1,, ?Δ2)%B                   => add_item (CtxCommaL Δ2) K Δ1
    | (?Δ1,, ?Δ2)%B                   => add_item (CtxCommaR Δ1) K Δ2
    | (?Δ1;, ?Δ2)%B                   => add_item (CtxSemicL Δ2) K Δ1
    | (?Δ1;, ?Δ2)%B                   => add_item (CtxSemicR Δ1) K Δ2
    end
  with add_item Ki K e := go (Ki :: K) e
  in
  go (@nil bunch_ctx_item) Δ.

Tactic Notation "bind_bunch" open_constr(Δ) :=
  match goal with
  | [ |- ?Σ ⊢ᴮ _ ] =>
    reshape_bunch Σ ltac:(fun Γ Δ' => unify Δ Δ'; change Σ with (fill Γ Δ))
  end.

Lemma id_ext (ϕ : formula) : frml ϕ ⊢ᴮ ϕ.
Proof.
  induction ϕ; try by constructor.
  - bind_bunch (frml _); apply BI_Emp_L. apply BI_Emp_R.
  - bind_bunch (frml _); apply BI_False_L.
  - bind_bunch (frml _); apply BI_Conj_L.
    by apply BI_Conj_R.
  - bind_bunch (frml _); apply BI_Sep_L.
    by apply BI_Sep_R.
  - apply BI_Impl_R.
    eapply BI_Equiv.
    { apply BE_semic_comm. }
    bind_bunch (_ ;, _)%B.
    by apply BI_Impl_L.
  - apply BI_Wand_R.
    eapply BI_Equiv.
    { apply BE_comma_comm. }
    bind_bunch (_ ,, _)%B.
    by apply BI_Wand_L.
Defined.


(** ** Alternative representation of decomposition of bunches *)
(** We have an inductive type that characterizes when a bunch can be
  decomposed into a context and a sub-bunch. This essentially gives an
  us an inductive reasoning principle for equations [fill Π Δ = Δ']. *)
Inductive bunch_decomp :
  bunch → bunch_ctx → bunch → Type :=
| decomp_id Δ : bunch_decomp Δ [] Δ
| decomp_comma_1 Δ1 Δ2 Π Δ :
    bunch_decomp Δ1 Π Δ →
    bunch_decomp (Δ1,,Δ2)%B (Π ++ [CtxCommaL Δ2]) Δ
| decomp_comma_2 Δ1 Δ2 Π Δ :
    bunch_decomp Δ2 Π Δ →
    bunch_decomp (Δ1,,Δ2)%B (Π ++ [CtxCommaR Δ1]) Δ
| decomp_semic_1 Δ1 Δ2 Π Δ :
    bunch_decomp Δ1 Π Δ →
    bunch_decomp (Δ1;,Δ2)%B (Π ++ [CtxSemicL Δ2]) Δ
| decomp_semic_2 Δ1 Δ2 Π Δ :
    bunch_decomp Δ2 Π Δ →
    bunch_decomp (Δ1;,Δ2)%B (Π ++ [CtxSemicR Δ1]) Δ.

(** * Properties *)

Lemma fill_app (Π Π' : bunch_ctx) (Δ : bunch) :
  fill (Π ++ Π') Δ = fill Π' (fill Π Δ).
Proof. by rewrite /fill foldl_app. Qed.

Lemma bunch_decomp_app C C0 Δ Δ0 :
  bunch_decomp Δ C0 Δ0 →
  bunch_decomp (fill C Δ) (C0 ++ C) Δ0.
Proof.
  revert Δ Δ0 C0.
  induction C as [|F C]=>Δ Δ0 C0.
  { simpl. by rewrite app_nil_r. }
  intros HD.
  replace (C0 ++ F :: C) with ((C0 ++ [F]) ++ C); last first.
  { by rewrite -assoc. }
  apply IHC. destruct F; simpl; by econstructor.
Qed.

Lemma bunch_decomp_correct Δ Π Δ' :
  bunch_decomp Δ Π Δ' → Δ = fill Π Δ'.
Proof. induction 1; rewrite ?fill_app /= //; try by f_equiv. Qed.

Lemma bunch_decomp_complete' Π Δ' :
  bunch_decomp (fill Π Δ') Π Δ'.
Proof.
  revert Δ'. remember (reverse Π) as Πr.
  revert Π HeqΠr.
  induction Πr as [|HΠ Πr]=>Π HeqΠr.
  { assert (Π = []) as ->.
    {  by eapply (inj reverse). }
    simpl. intros. econstructor. }
  intros Δ'.
  assert (Π = reverse Πr ++ [HΠ]) as ->.
  { by rewrite -reverse_cons HeqΠr reverse_involutive. }
  rewrite fill_app /=.
  revert Δ'.
  induction HΠ=>Δ' /=; econstructor; eapply IHΠr; by rewrite reverse_involutive.
Defined.

Lemma bunch_decomp_complete Δ Π Δ' :
  (fill Π Δ' = Δ) →
  bunch_decomp Δ Π Δ'.
Proof. intros <-. apply bunch_decomp_complete'. Defined.

Lemma bunch_decomp_ctx Γ Γ' Δ ϕ :
  bunch_decomp (fill Γ Δ) Γ' (frml ϕ) →
  { Γ₀ : bunch_ctx & (bunch_decomp Δ Γ₀ (frml ϕ) * (Γ' = Γ₀ ++ Γ))%type}
  + { '(Γ₀, Γ₁) & ((∀ Δ', bunch_decomp (fill Γ Δ') (Γ₀ Δ') (frml ϕ)) *
         (∀ Δ Δ', fill (Γ₀ Δ) Δ' = fill (Γ₁ Δ') Δ) *
         (∀ Δ', fill (Γ₁ Δ') Δ = fill Γ' Δ'))%type }.
Proof.
  revert Δ Γ'.
  induction Γ as [|F Γ]=>Δ Γ'; simpl.
  { remember (frml ϕ) as Γ1. intros Hdec.
    left. eexists. rewrite right_id. split; done. }
  simpl. intros Hdec.
  destruct (IHΓ _ _ Hdec) as [IH|IH].
  - destruct IH as [Γ₀ [HΓ₀ HΓ]].
    destruct F; simpl in *.
    + inversion HΓ₀; simplify_eq/=.
      * left. exists Π.
        split; simpl; eauto.
        rewrite -assoc //.
      * right.
        exists
          ((λ A, (Π ++ [CtxCommaR A]) ++ Γ),
           (λ A, ([CtxCommaL (fill Π A)] ++ Γ))).
        repeat split.
        { intros A. apply bunch_decomp_app. by econstructor. }
        { intros A B. by rewrite /= -!assoc /= !fill_app. }
        { intros A. by rewrite /= -!assoc /= !fill_app. }
    + inversion HΓ₀; simplify_eq/=.
      * right.
        exists
          ((λ A, (Π ++ [CtxCommaL A]) ++ Γ)
          ,(λ A, ([CtxCommaR (fill Π A)] ++ Γ))).
        repeat split.
        { intros A. apply bunch_decomp_app. by econstructor. }
        { intros A B. by rewrite /= -!assoc /= !fill_app. }
        { intros A. by rewrite /= -!assoc /= !fill_app. }
      * left. eexists; split; eauto.
        rewrite -assoc //.
    + inversion HΓ₀; simplify_eq/=.
      * left. exists Π.
        split; simpl; eauto.
        rewrite -assoc //.
      * right.
        exists
          ((λ A, (Π ++ [CtxSemicR A]) ++ Γ),
           (λ A, ([CtxSemicL (fill Π A)] ++ Γ))).
        repeat split.
        { intros A. apply bunch_decomp_app. by econstructor. }
        { intros A B. by rewrite /= -!assoc /= !fill_app. }
        { intros A. by rewrite /= -!assoc /= !fill_app. }
    + inversion HΓ₀; simplify_eq/=.
      * right.
        exists
          ((λ A, (Π ++ [CtxSemicL A]) ++ Γ),
           (λ A, ([CtxSemicR (fill Π A)] ++ Γ))).
        repeat split.
        { intros A. apply bunch_decomp_app. by econstructor. }
        { intros A B. by rewrite /= -!assoc /= !fill_app. }
        { intros A. by rewrite /= -!assoc /= !fill_app. }
      * left. exists Π.
        split; simpl; eauto.
        rewrite -assoc //.
  - right.
    destruct IH as ([Γ₀ Γ₁] & [[HΓ HΓ₀] HΓ₁]).
    exists ((λ A, Γ₀ (fill_item F A)), (λ A, F::Γ₁ A)). repeat split.
    { intros A. apply HΓ. }
    { intros A B. simpl. rewrite -HΓ₀ //. }
    { intros B. rewrite -HΓ₁ //. }
Defined.


Notation "Δ ';,' Γ" := (semic Δ%B Γ%B) (at level 80, right associativity) : bunch_scope.
Notation "Δ ',,' Γ" := (comma Δ%B Γ%B) (at level 80, right associativity) : bunch_scope.
