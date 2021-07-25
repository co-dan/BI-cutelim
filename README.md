A semantic cut admissibility proof for the logic of Bunched Implications and extensions.

We formalize the sequent calculus of BI and give an algebraic proof of
cut admissibility. We parametrize the calculus by an arbitrary
collection of "simple structural rules" (see `theories/seqcalc.v` for
the definition).

Structure:
- `syntax.v`, `terms.v` -- formulas of BI and "bunched terms".
  A bunched term is essential a formula built up only from `∗/,` and
  `∧/;` and variables.
- `interp.v` -- interpretation of formulas and bunched terms in a BI algebra
- `seqcalc.v` -- sequent calculus + soundness
- `bunch_decomp.v` -- helpful lemmas about decompositions of bunches
- `seqcalc_height.v` -- the same sequent calculus, but with the notion of proof height.
  Includes proofs of invertibility of some of the rules.
- `cutelim.v` -- the universal model for cut elimination

We can adapt the same method to modal BI, by "freely" adding an S4-like box modality.
See `seqcalc_s4.v`, `cutelim_s4.v` etc.
