From stdpp Require Import prelude base gmap fin_sets.

Section preimage.
  Context `{FinMap K MK, FinMap A MA, FinSet K SK, !LeibnizEquiv SK}.
  Local Notation map_preimage :=
    (map_preimage (K:=K) (A:=A) (MKA:=MK A) (MASK:=MA SK) (SK:=SK)).
  Implicit Types m : MK A.

  Lemma map_preimage_singleton i x : map_preimage {[i:=x]} = {[x:={[i]}]}.
  Proof.
    apply map_eq. intro y.
    rewrite <- insert_empty. rewrite map_preimage_insert; [ | apply lookup_empty ].
    destruct (decide (x = y)) as [->|Hxy].
    - rewrite lookup_singleton.
      rewrite map_preimage_empty. rewrite lookup_partial_alter, lookup_empty.
      simpl. f_equal. apply right_id. apply _.
    - rewrite lookup_singleton_ne; auto.
      rewrite lookup_partial_alter_ne; auto.
      rewrite map_preimage_empty. apply lookup_empty.
  Qed.
End preimage.

(** * [set_map_2] *)
Section set_map_2.
  Context {A B C : Type}.
  Context `{!EqDecision A, !Countable A, !EqDecision B, !Countable B}.
  Context `{!EqDecision C, !Countable C}.

  Definition set_map_2 `{Elements A SA, Elements B SB, Singleton C SC, Empty SC, Union SC}
    (f : A → B → C) (X : SA) (Y : SB) : SC :=
    set_bind (λ x, set_bind (λ y, {[ f x y ]} ) Y) X.
  Typeclasses Opaque set_map_2.

  Lemma elem_of_set_map_2 (f : A → B → C) (X : gset A) (Y : gset B) (z : C) :
    z ∈ (set_map_2 f X Y : gset C) ↔ ∃ x y, z = f x y ∧ x ∈ X ∧ y ∈ Y.
  Proof. unfold set_map_2. set_solver. Qed.
  Global Instance set_unfold_map (f : A → B → C) (X : gset A) (Y : gset B) (z : C) P Q :
    (∀ x, SetUnfoldElemOf x X (P x)) →
    (∀ y, SetUnfoldElemOf y Y (Q y)) →
    SetUnfoldElemOf z (set_map_2 (SC:=gset C) f X Y) (∃ x y, z = f x y ∧ P x ∧ Q y).
  Proof. intros ? ?. constructor. rewrite elem_of_set_map_2; set_solver. Qed.
End set_map_2.

