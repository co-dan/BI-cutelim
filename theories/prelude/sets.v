From stdpp Require Import prelude base gmap fin_sets.

(** * Preimage of a [FinMap] *)
(* This is copied form the MR [https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/382/] *)

(** Given a finite map [m] with keys [K] and values [A], the preimage
[map_preimage m] gives a finite map with keys [A] and values set [A]. The type
of [map_preimage] is very generic to support different map and set
implementations. A possible instance is [MKA:=gmap K A], [MADK:=gmap A (gset K)],
and [DK:=gset K]. *)
Definition map_preimage `{FinMapToList K A MKA, Empty MADK,
    PartialAlter A DK MADK, Empty DK, Singleton K DK, Union DK}
    (m : MKA) : MADK :=
  map_fold (λ i, partial_alter (λ mX, Some $ {[ i ]} ∪ default ∅ mX)) ∅ m.
Typeclasses Opaque map_preimage.

Section preimage.
  (** We restrict the theory to finite sets with Leibniz equality, which is
  sufficient for [gset], but not for [boolset] or [propset]. The result of the
  pre-image is a map of sets. To support general sets, we need setoid equality
  on sets, and thus setoid equality on maps. *)
  Context `{FinMap K MK, FinMap A MA, FinSet K DK, !LeibnizEquiv DK}.
  Local Notation map_preimage :=
    (map_preimage (K:=K) (A:=A) (MKA:=MK A) (MADK:=MA DK) (DK:=DK)).
  Implicit Types m : MK A.

  Lemma map_preimage_empty : map_preimage ∅ = ∅.
  Proof. apply map_fold_empty. Qed.
  Lemma map_preimage_insert m i x :
    m !! i = None →
    map_preimage (<[i:=x]> m) =
      partial_alter (λ mX, Some ({[ i ]} ∪ default ∅ mX)) x (map_preimage m).
  Proof.
    intros Hi. refine (map_fold_insert_L _ _ i x m _ Hi).
    intros j1 j2 x1 x2 m' ? _ _. destruct (decide (x1 = x2)) as [->|?].
    - rewrite <-!partial_alter_compose.
      apply partial_alter_ext; intros ? _; f_equal/=. set_solver.
    - by apply partial_alter_commute.
  Qed.

  Lemma lookup_preimage_Some_empty m x :
    map_preimage m !! x ≠ Some ∅.
  Proof.
    induction m as [|i x' m ? IH] using map_ind.
    { by rewrite map_preimage_empty, lookup_empty. }
    rewrite map_preimage_insert by done. destruct (decide (x = x')) as [->|].
    - rewrite lookup_partial_alter. intros [=]. set_solver.
    - rewrite lookup_partial_alter_ne by done. set_solver.
  Qed.

  Lemma lookup_preimage_None_1 m x i :
    map_preimage m !! x = None → m !! i ≠ Some x.
  Proof.
    induction m as [|i' x' m ? IH] using map_ind; [by rewrite lookup_empty|].
    rewrite map_preimage_insert by done. destruct (decide (x = x')) as [->|].
    - by rewrite lookup_partial_alter.
    - rewrite lookup_partial_alter_ne, lookup_insert_Some by done. naive_solver.
  Qed.

  Lemma lookup_preimage_Some_1 m X x i :
    map_preimage m !! x = Some X →
    i ∈ X ↔ m !! i = Some x.
  Proof.
    revert X. induction m as [|i' x' m ? IH] using map_ind; intros X.
    { by rewrite map_preimage_empty, lookup_empty. }
    rewrite map_preimage_insert by done. destruct (decide (x = x')) as [->|].
    - rewrite lookup_partial_alter. intros [= <-].
      rewrite elem_of_union, elem_of_singleton, lookup_insert_Some.
      destruct (map_preimage m !! x') as [X'|] eqn:Hx'; simpl.
      + rewrite IH by done. naive_solver.
      + apply (lookup_preimage_None_1 _ _ i) in Hx'. set_solver.
    - rewrite lookup_partial_alter_ne, lookup_insert_Some by done. naive_solver.
  Qed.

  Lemma lookup_preimage_None m x :
    map_preimage m !! x = None ↔ ∀ i, m !! i ≠ Some x.
  Proof.
    split; [by eauto using lookup_preimage_None_1|].
    intros Hm. apply eq_None_not_Some; intros [X ?].
    destruct (set_choose_L X) as [i ?].
    { intros ->. by eapply lookup_preimage_Some_empty. }
    by eapply (Hm i), lookup_preimage_Some_1.
  Qed.

  Lemma lookup_preimage_Some m x X :
    map_preimage m !! x = Some X ↔ X ≠ ∅ ∧ ∀ i, i ∈ X ↔ m !! i = Some x.
  Proof.
    split.
    - intros HxX. split; [intros ->; by eapply lookup_preimage_Some_empty|].
      intros j. by apply lookup_preimage_Some_1.
    - intros [HXne HX]. destruct (map_preimage m !! x) as [X'|] eqn:HX'.
      + f_equal; apply set_eq; intros i. rewrite HX.
        by apply lookup_preimage_Some_1.
      + apply set_choose_L in HXne as [j ?].
        apply (lookup_preimage_None_1 _ _ j) in HX'. naive_solver.
  Qed.

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

  (** XXX This is not part of the MR.. yet? *)
  Lemma lookup_total_preimage `{EqDecision DK} m i x :
    i ∈ (map_preimage m !!! x) ↔ m !! i = Some x.
  Proof.
    rewrite lookup_total_alt.
    destruct (map_preimage m !! x) as [X'|] eqn:Hp; simpl.
    - by apply lookup_preimage_Some.
    - apply (lookup_preimage_None_1 _ _ i) in Hp.
      set_solver.
  Qed.

End preimage.

(** * [set_map_2] *)

Definition list_ap {A B} (fs : list (A → B)) (xs : list A) : list B :=
  f ← fs;
  x ← xs;
  [f x].

Section gset_ap.
  Context {A B C : Type}.
  Context `{!EqDecision A, !Countable A, !EqDecision B, !Countable B}.
  Context `{!EqDecision C, !Countable C}.

  Definition set_map_2 (f : A → B → C) (X : gset A) (Y : gset B) : gset C :=
    list_to_set (list_ap (map f (elements X)) (elements Y)).
  Typeclasses Opaque set_map_2.

  Lemma elem_of_map_2 (f : A → B → C) (X : gset A) (Y : gset B) z :
    z ∈ set_map_2 f X Y ↔ ∃ x y, z = f x y ∧ x ∈ X ∧ y ∈ Y.
  Proof.
    unfold set_map_2. rewrite elem_of_list_to_set.
    unfold list_ap. rewrite list_fmap_bind.
    rewrite elem_of_list_bind. set_solver.
  Qed.
  (* Global Instance set_unfold_map (f : A → B) (X : C) (P : A → Prop) y : *)
  (*   (∀ x, SetUnfoldElemOf x X (P x)) → *)
  (*   SetUnfoldElemOf y (set_map (D:=D) f X) (∃ x, y = f x ∧ P x). *)
  (* Proof. constructor. rewrite elem_of_map; naive_solver. Qed. *)
End gset_ap.
Global Instance: Params (@set_map_2) 12 := {}.
