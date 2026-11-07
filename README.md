# Twisted conjugacy in spherical Artin groups and their crystallographic quotients

This repository proves property R∞ for the Artin groups of types D5, E6, E7, E8, F4, H3 and H4: every automorphism has infinitely many twisted conjugacy classes. The proof does not need a classification of Aut(A).

Together with earlier work, this shows that every irreducible spherical Artin group of rank at least 2 has R∞. That settles the spherical case of AIM problem list "Geometry of Artin groups", Problem 8.6. The same method also gives uniform proofs in types A_n, B_n and D_n.

The manuscript now presents three headline results:

- **Theorem A:** the spherical Artin-group classification above.
- **Theorem B:** a complete classification of the irreducible spherical crystallographic quotients A(X)/[P,P]. Every rank ≥ 3 has R∞. In rank two, I₂(m) has R∞ exactly when 4 divides m, or m is odd and 3 divides m.
- **Proposition C:** A(I₂(5))/[P,P] has an explicit automorphism with **R = 18**, so the quotient construction does not preserve R∞.

The earlier exploratory dihedral script reported 14 by using a torsion-free determinant average. The actual I₂(5) quotient has torsion; a direct count gives 18. The proof and an independent exact enumeration are in §6.7 and `code/indep/dihedral_quotient.py`.

The full quotient classification has uniform proofs: character equations and class sizes for B_n/D_n, the frame constituent for D4, and stable/swap witnesses or explicit affine automorphisms for every dihedral parameter. Finite checks support these proofs; no unbounded statement is inferred from checking a bounded range. Theorem B also gives another proof of Theorem A, using characteristicity and the known dihedral Artin-group result, without the Franzsen–Howlett automorphism decomposition.

On D5:
- Soroko–Vaskou (arXiv:2409.18123v2) leave D5 open.
- Paris–Soroko compute Aut(A[D5]). R∞ follows from this by a short argument (Remark 5.3), which they do not state.
- Soroko 2026 lists D5, attributing it to Soroko–Vaskou.

The paper gives a proof by its own method (Prop 5.2).

## Contents

| Path | What it holds |
|---|---|
| `paper/` | Manuscript, version 5 (`main.tex`, `main.pdf`), including the full quotient classification and corrected dihedral count |
| `code/` | Computational certificates and independent checkers, including those of the internal AI referees. `code/README.md` has the commands, expected outputs and the correspondence between old (v2) and new (v3) theorem numbers. |
| `lean/` | Lean 4 / Mathlib formalisation. See `lean/README.md`. |
| `AUDIT.md` | Claim-by-claim audit, the response tables for the referee and the external review, and open items |
| `REVIEWER_NOTE.md` | One-page note for human reviewers |
| `provenance/` | Earlier drafts and the internal referee summary |

## Structure of the proof (paper v5)

1. **The characteristic reflection lattice.** P = ker(A → W) is characteristic (Cohen–Paris). H₁(P; ℤ) ≅ ℤ^T is the permutation lattice on the reflections.
2. **The fixed-vector criterion** (Thm 3.3). Schur's lemma on a rational, absolutely irreducible, multiplicity-one constituent forces the commuting part to act by ±1. Sign or swap witnesses then give a fixed vector after an inner twist.
3. **Exceptional types** (§4).
   - The induced automorphisms of W/Z come from Aut(W), which is controlled by Franzsen–Howlett, Thm 31.
   - The constituents are explicit:
     - strongly regular graph eigenspaces for E_n;
     - frame modules for H3 and F4;
     - matrix coefficients in the icosian model for H4.
4. **Classical types** (§5): A_n, B_n, D_n by hand, including D5. For the dihedral types I2(m) the method has a limitation, which §5 explains.
5. **Crystallographic quotients** (§6): a credited lattice criterion; the seven initial positive cases; uniform classical proofs; the odd-dimensional alternative for D5/E6/E7/E8/H4; extension compatibility; the complete dihedral classification; and Proposition C. The further question is the Reidemeister spectra in the negative dihedral families.
6. **Appendices.**
   - Appendix A separates the proof certificates (exact, asserting scripts) from corroboration (some of it numerical).
   - Appendix B gives the stronger statement about all of Aut(W/Z): computed for E6, E7, F4, H3, H4 and D5, and proved by hand for E8. These are proof inputs for the seven-case component in §6.2 (formerly Cor. B.3). The classical-family argument needs only character-preserving holonomy automorphisms.
   - In Lean, the full Aut(W/Z) statement appears only as the hypothesis `hOut` of the legacy theorems `artin_X_R_infty` (proved there for H3 and F4). The main theorems `artin_X_R_infty_FH` do not need it.

## Lean formalisation

The quotient results in §6, including the full classification and Proposition C, are not Lean-formalised. Exact SymPy checks can be run with `python3 code/indep/dihedral_quotient.py` and `python3 code/indep/quotient_families.py --max-m 46`.

To build: `cd lean && lake build`. A clean build takes about 12 minutes with 4 threads and the Mathlib v4.35.0 cache (as of commit 296176a). Peak memory is about 25 GB for the largest certificate modules and about 11 GB for the Franzsen–Howlett search-tree modules. The development contains no `sorry`, no `native_decide` and no `axiom`; it depends only on `propext`, `Classical.choice` and `Quot.sound`. See `lean/README.md`.

The Lean kernel checks:
- Reidemeister numbers and the basic lemmas;
- the abstract criterion, including the swap case;
- Artin groups as presented groups, the map to ℤ^T ⋊ Perm T, and the equivariant structure of P^ab;
- the finite certificates for all seven types D5, E6, E7, E8, F4, H3, H4;
- the finite part of Lemma 4.1, a search-tree certificate that every reflection-preserving automorphism of W/Z is inner or inner times π₀;
- Out(W/Z) for H3 and F4, by enumeration.

For each of the seven types the final theorem `artin_X_R_infty_FH` has exactly four hypotheses, the cited inputs:
- `hW`: W is finite.
- `hCP`: P is characteristic (Cohen–Paris, itself computer-assisted).
- `hBr`: P^ab ≅ ℤ^N as groups, with N = |T| (Brieskorn).
- `hFH`: Aut(W) = R(W)·A(W) (Franzsen–Howlett, Thm 31; for D5, Thm 31(3)).

For H3 and F4 there are also versions needing only `hW`, `hCP` and `hBr`. The certificates use computer-found good constituents (for D5, the constituent U⁻ of Prop 5.2), not the explicit constructions of §4.

Mathlib's `CoxeterMatrix.D 5` is not the D5 matrix in this Mathlib version: it contains a triangle. So D5 uses an explicitly defined Coxeter matrix (`lean/ArtinRinf/CoxD5.lean`).

## Status

The proofs, code, Lean development and manuscript were developed with substantial AI assistance. So far they have been reviewed only by AI systems:
- an internal audit;
- two rounds of an AI "cold referee";
- external AI reviews, including reviews of the code and Lean sources and the latest quotient-focused review.

None of this is journal peer review, and no human expert has verified the work yet.
