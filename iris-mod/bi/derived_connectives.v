From iris.algebra Require Import monoid.
From iris_mod.bi Require Export interface.
From iris.prelude Require Import options.

Definition bi_iff {PROP : bi} (P Q : PROP) : PROP := (P → Q) ∧ (Q → P).
Global Arguments bi_iff {_} _%I _%I : simpl never.
Global Instance: Params (@bi_iff) 1 := {}.
Infix "↔" := bi_iff : bi_scope.

Definition bi_wand_iff {PROP : bi} (P Q : PROP) : PROP :=
  (P -∗ Q) ∧ (Q -∗ P).
Global Arguments bi_wand_iff {_} _%I _%I : simpl never.
Global Instance: Params (@bi_wand_iff) 1 := {}.
Infix "∗-∗" := bi_wand_iff : bi_scope.

Definition bi_affinely {PROP : bi} (P : PROP) : PROP := emp ∧ P.
Global Arguments bi_affinely {_} _%I : simpl never.
Global Instance: Params (@bi_affinely) 1 := {}.
Typeclasses Opaque bi_affinely.
Notation "'<affine>' P" := (bi_affinely P) : bi_scope.

Class Affine {PROP : bi} (Q : PROP) := affine : Q ⊢ emp.
Global Arguments Affine {_} _%I : simpl never.
Global Arguments affine {_} _%I {_}.
Global Hint Mode Affine + ! : typeclass_instances.

Definition bi_absorbingly {PROP : bi} (P : PROP) : PROP := True ∗ P.
Global Arguments bi_absorbingly {_} _%I : simpl never.
Global Instance: Params (@bi_absorbingly) 1 := {}.
Typeclasses Opaque bi_absorbingly.
Notation "'<absorb>' P" := (bi_absorbingly P) : bi_scope.

Class Absorbing {PROP : bi} (P : PROP) := absorbing : <absorb> P ⊢ P.
Global Arguments Absorbing {_} _%I : simpl never.
Global Arguments absorbing {_} _%I.
Global Hint Mode Absorbing + ! : typeclass_instances.


Definition bi_affinely_if {PROP : bi} (p : bool) (P : PROP) : PROP :=
  (if p then <affine> P else P)%I.
Global Arguments bi_affinely_if {_} !_ _%I /.
Global Instance: Params (@bi_affinely_if) 2 := {}.
Typeclasses Opaque bi_affinely_if.
Notation "'<affine>?' p P" := (bi_affinely_if p P) : bi_scope.

Definition bi_absorbingly_if {PROP : bi} (p : bool) (P : PROP) : PROP :=
  (if p then <absorb> P else P)%I.
Global Arguments bi_absorbingly_if {_} !_ _%I /.
Global Instance: Params (@bi_absorbingly_if) 2 := {}.
Typeclasses Opaque bi_absorbingly_if.
Notation "'<absorb>?' p P" := (bi_absorbingly_if p P) : bi_scope.

Fixpoint bi_laterN {PROP : bi} (n : nat) (P : PROP) : PROP :=
  match n with
  | O => P
  | S n' => ▷ ▷^n' P
  end
where "▷^ n P" := (bi_laterN n P) : bi_scope.
Global Arguments bi_laterN {_} !_%nat_scope _%I.
Global Instance: Params (@bi_laterN) 2 := {}.
Notation "▷? p P" := (bi_laterN (Nat.b2n p) P) : bi_scope.

Definition bi_except_0 {PROP : bi} (P : PROP) : PROP := ▷ False ∨ P.
Global Arguments bi_except_0 {_} _%I : simpl never.
Notation "◇ P" := (bi_except_0 P) : bi_scope.
Global Instance: Params (@bi_except_0) 1 := {}.
Typeclasses Opaque bi_except_0.

Class Timeless {PROP : bi} (P : PROP) := timeless : ▷ P ⊢ ◇ P.
Global Arguments Timeless {_} _%I : simpl never.
Global Arguments timeless {_} _%I {_}.
Global Hint Mode Timeless + ! : typeclass_instances.
Global Instance: Params (@Timeless) 1 := {}.

(** An optional precondition [mP] to [Q].
    TODO: We may actually consider generalizing this to a list of preconditions,
    and e.g. also using it for texan triples. *)
Definition bi_wandM {PROP : bi} (mP : option PROP) (Q : PROP) : PROP :=
  match mP with
  | None => Q
  | Some P => P -∗ Q
  end.
Global Arguments bi_wandM {_} !_%I _%I /.
Notation "mP -∗? Q" := (bi_wandM mP Q)
  (at level 99, Q at level 200, right associativity) : bi_scope.
