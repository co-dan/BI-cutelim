(* This file has been copied & adapted from the Iris Coq formalization.
   See the `theories/algebra/bi` subdirectory therein.
*)
From bunched.algebra Require Export interface derived_laws.
From stdpp Require Import prelude.

Instance Prop_equiv : Equiv Prop := iff.
Instance Prop_equivalence : Equivalence (≡@{Prop}) := _.

Module Import bi.
  Export interface.bi.
  Export derived_laws.bi.
End bi.
