A semantic cut admissibility proof for the logic of Bunched Implications and extensions.

## Intro

We formalize the sequent calculus of BI and give an algebraic proof of
cut admissibility. We parametrize the calculus by an arbitrary
collection of "simple structural rules" (see `theories/seqcalc.v` for
the definition).

Structure (in the `theories` directory):
- `syntax.v`, `terms.v` -- formulas of BI and "bunched terms".
  A bunched term is essential a formula built up only from `∗/,` and
  `∧/;` and variables.
- `interp.v` -- interpretation of formulas and bunched terms in a BI algebra
- `seqcalc.v` -- sequent calculus + soundness
- `bunch_decomp.v` -- helpful lemmas about decompositions of bunches
- `seqcalc_height.v` -- the same sequent calculus, but with the notion of proof height.
  Includes proofs of invertibility of some of the rules.
- `cutelim.v` -- the universal model for cut elimination
- `algebra/bi.v`, `algebra/interface.v` -- BI algebras

There is also a formalization of the same method for BI with an S4-like box modality.
See `seqcalc_s4.v`, `seqcalc_height_s4.v`, `interp_s4.v`, and `cutelim_s4.v` in the `theories` folder.

## Compilation

You will need a copy of Equations and std++ installed.
You can install the dependencies with opam using `opam install --deps-only .` or the whole developement with `opam install .`

If you have the dependencies installed then you can compile the project with `make -jN` where `N` is the number of threads you want to use.
Compile the HTML docs with `make html`.



## Copyright

The Coq formalization is distributed under the BSD-3 licence.
The code in the `theories/algebra` folder is adapted from
the Iris project <https://iris-project.org>
