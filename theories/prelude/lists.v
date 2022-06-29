From stdpp Require Import prelude base list.

Lemma Forall_exists_Forall2 A B : forall (P : A → B → Prop) l,
    Forall (fun y => exists x, P x y) l <-> exists l', Forall2 P l' l.
Proof.
  induction l as [|x l IHl]; split; intros HF.
  - eexists; econstructor.
  - constructor.
  - inversion_clear HF as [| ? ? [y Hy] HFtl]; subst.
    destruct (proj1 IHl HFtl) as [l' Hl'].
    exists (y :: l'). by econstructor.
  - destruct HF as [? HF%Forall2_cons_inv_r].
    destruct HF as (y & l' & Hy & HF & ->).
    econstructor; eauto.
    apply IHl. eauto.
Qed.
