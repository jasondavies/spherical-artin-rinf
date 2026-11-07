# Twisted conjugacy in irreducible spherical Artin groups

This repository proves property R∞ for the Artin groups of types D5, E6, E7, E8, F4, H3 and H4: every automorphism has infinitely many twisted conjugacy classes. The proof does not need a classification of Aut(A).

Together with earlier work, this shows that every irreducible spherical Artin group of rank at least 2 has R∞. That settles the spherical case of AIM problem list "Geometry of Artin groups", Problem 8.6. The same method also gives uniform proofs in types A_n, B_n and D_n.

These cases were already known except D5. Soroko–Vaskou (arXiv:2409.18123v2) prove D_n only for n ≥ 6 and conjecture D5, and Paris–Soroko compute Aut(A[D5]) without stating R∞. Two proofs of D5 are given: paper Prop 5.2, and a short deduction from Paris–Soroko's Thm 1 (Remark 5.3).

## Contents

| Path | What it holds |
|---|---|
| `paper/` | Manuscript, version 3 (`main.tex`, `main.pdf`), revised after an external (AI) review |
| `code/` | Computational certificates and independent checkers, including those of the internal AI referees. `code/README.md` has the commands, expected outputs and the correspondence between old (v2) and new (v3) theorem numbers. |
| `lean/` | Lean 4 / Mathlib formalisation. See `lean/README.md`, which uses the **v2** theorem numbering. |
| `AUDIT.md` | Claim-by-claim audit, the response tables for the referee and the external review, and open items |
| `REVIEWER_NOTE.md` | One-page note for human reviewers |
| `provenance/` | Earlier drafts and the internal referee summary |

## Structure of the proof (paper v3)

1. **The characteristic reflection lattice.** P = ker(A → W) is characteristic (Cohen–Paris). H₁(P; ℤ) ≅ ℤ^T is the permutation lattice on the reflections.
2. **The fixed-vector criterion** (Thm 3.3). Schur's lemma on a rational, absolutely irreducible, multiplicity-one constituent forces the commuting part to act by ±1. Sign or swap witnesses then give a fixed vector after an inner twist.
3. **Exceptional types** (§4).
   - The induced automorphisms of W/Z come from Aut(W), which is controlled by Franzsen–Howlett, Thm 31.
   - The constituents are explicit:
     - strongly regular graph eigenspaces for E_n;
     - frame modules for H3 and F4;
     - matrix coefficients in the icosian model for H4.
4. **Classical types** (§5): A_n, B_n, D_n by hand, including the new case D5. For the dihedral types I2(m) the method has a limitation, which §5 explains.
5. **Appendices.**
   - Appendix A lists the computational cross-checks.
   - Appendix B gives the stronger statement about all of Aut(W/Z). This is the hypothesis `hOut` used in Lean; for E8 it is proved by hand.

## Lean formalisation

To build: `cd lean && lake build`. A clean build takes about 11 minutes with 4 threads and the Mathlib v4.35.0 cache. The development contains no `sorry`, no `native_decide` and no `axiom`; it depends only on `propext`, `Classical.choice` and `Quot.sound`.

The Lean kernel checks:
- Reidemeister numbers and the basic lemmas;
- the abstract criterion, including the swap case;
- Artin groups as presented groups, the map to ℤ^T ⋊ Perm T, and the equivariant structure of P^ab;
- the finite certificates for all six exceptional types;
- Out(W/Z) for H3 and F4.

The following enter as explicit hypotheses:
- `hW`: W is finite.
- `hCP`: P is characteristic (Cohen–Paris, itself computer-assisted).
- `hBr`: P^ab ≅ ℤ^N as groups, with N = |T| (Brieskorn).
- `hOut`: every automorphism of W/Z is inner or inner times π₀. This is proved in Lean for H3 and F4, and remains a hypothesis for H4, E6, E7 and E8.

The formalisation uses `hOut`, which is stronger than the Franzsen–Howlett-based argument of paper v3. Its certificates are the computer-found constituents, not the explicit constructions of §4.

## Status

The proofs, code, Lean development and manuscript were developed with substantial AI assistance. So far they have been reviewed only by AI systems:
- an internal audit;
- two rounds of an AI "cold referee";
- an external AI review of the manuscript.

None of this is journal peer review, and no human expert has verified the work yet.## Lean formalization

Build it with `cd lean && lake build`. A clean build takes about 12 minutes with 4 threads (Mathlib v4.35.0 cache), and some processes use about 11 GB of RAM. The development has no `sorry`, no `native_decide` and no `axiom`. All 24 main declarations depend only on `propext`, `Classical.choice` and `Quot.sound`.

The Lean kernel checks:
- the Reidemeister lemmas;
- the fixed-vector criterion;
- Artin groups as presented groups, with the map to ℤ^T ⋊ Perm T;
- the equivariant structure of P^ab;
- finite certificates for H3, F4, H4, E6, E7 and E8;
- the finite part of Lemma 4.1: every reflection-preserving automorphism of W/Z lies in ρ(W)⟨π₀⟩. This is shown by a search-tree certificate.

For each of the six types, `artin_X_R_infty_FH` has exactly four hypotheses, which are the cited theorems:
- `hW`: W is finite;
- `hCP`: P is characteristic (Cohen–Paris);
- `hBr`: P^ab ≅ ℤ^|T| (Brieskorn);
- `hFH`: Aut(W) = R(W)·A(W) (Franzsen–Howlett, Thm 31).

See `lean/README.md` for details.

## Contents

| Path | What it holds |
|---|---|
| `paper/` | Manuscript, version 3 (`main.tex`, `main.pdf`), revised after an external (AI) review |
| `code/` | Computational certificates and independent checkers, including those of the internal AI referees. `code/README.md` has the commands, expected outputs and the correspondence between old (v2) and new (v3) theorem numbers. |
| `lean/` | Lean 4 / Mathlib formalisation. See `lean/README.md`, which uses the **v2** theorem numbering. |
| `AUDIT.md` | Claim-by-claim audit, the response tables for the referee and the external review, and open items |
| `REVIEWER_NOTE.md` | One-page note for human reviewers |
| `provenance/` | Earlier drafts and the internal referee summary |

## Structure of the proof (paper v3)

1. **The characteristic reflection lattice.** P = ker(A → W) is characteristic (Cohen–Paris). H₁(P; ℤ) ≅ ℤ^T is the permutation lattice on the reflections.
2. **The fixed-vector criterion** (Thm 3.3). Schur's lemma on a rational, absolutely irreducible, multiplicity-one constituent forces the commuting part to act by ±1. Sign or swap witnesses then give a fixed vector after an inner twist.
3. **Exceptional types** (§4).
   - The induced automorphisms of W/Z come from Aut(W), which is controlled by Franzsen–Howlett, Thm 31.
   - The constituents are explicit:
     - strongly regular graph eigenspaces for E_n;
     - frame modules for H3 and F4;
     - matrix coefficients in the icosian model for H4.
4. **Classical types** (§5): A_n, B_n, D_n by hand, including the new case D5. For the dihedral types I2(m) the method has a limitation, which §5 explains.
5. **Appendices.**
   - Appendix A lists the computational cross-checks.
   - Appendix B gives the stronger statement about all of Aut(W/Z). This is the hypothesis `hOut` used in Lean; for E8 it is proved by hand.

## Lean formalisation

To build: `cd lean && lake build`. A clean build takes about 11 minutes with 4 threads and the Mathlib v4.35.0 cache. The development contains no `sorry`, no `native_decide` and no `axiom`; it depends only on `propext`, `Classical.choice` and `Quot.sound`.

The Lean kernel checks:
- Reidemeister numbers and the basic lemmas;
- the abstract criterion, including the swap case;
- Artin groups as presented groups, the map to ℤ^T ⋊ Perm T, and the equivariant structure of P^ab;
- the finite certificates for all six exceptional types;
- Out(W/Z) for H3 and F4.

The following enter as explicit hypotheses:
- `hW`: W is finite.
- `hCP`: P is characteristic (Cohen–Paris, itself computer-assisted).
- `hBr`: P^ab ≅ ℤ^N as groups, with N = |T| (Brieskorn).
- `hOut`: every automorphism of W/Z is inner or inner times π₀. This is proved in Lean for H3 and F4, and remains a hypothesis for H4, E6, E7 and E8.

The formalisation uses `hOut`, which is stronger than the Franzsen–Howlett-based argument of paper v3. Its certificates are the computer-found constituents, not the explicit constructions of §4.

## Status

The proofs, code, Lean development and manuscript were developed with substantial AI assistance. So far they have been reviewed only by AI systems:
- an internal audit;
- two rounds of an AI "cold referee";
- an external AI review of the manuscript.

None of this is journal peer review, and no human expert has verified the work yet.
