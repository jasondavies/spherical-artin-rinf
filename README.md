# Property R∞ for the exceptional spherical Artin groups

This repository proves property R∞ for the Artin groups of types E6, E7, E8, F4, H3 and H4. Property R∞ means that every automorphism has infinitely many twisted conjugacy classes. The proof does not require determining Aut(A).

Combined with earlier work, the result shows that every irreducible spherical Artin group of rank at least 2 has R∞. This settles the spherical case of AIM problem list "Geometry of Artin groups", Problem 8.6.

## Contents

| Path | What it holds |
|---|---|
| `paper/` | Manuscript (`main.tex`, `main.pdf`) |
| `code/` | Computational certificates and independent checkers. See `code/README.md` for commands and expected output. |
| `lean/` | Lean 4 / Mathlib formalization. See `lean/README.md`. |
| `AUDIT.md` | Claim-by-claim audit and the open items |
| `REVIEWER_NOTE.md` | One-page note for reviewers |
| `provenance/` | Earlier draft and the internal referee summary |

## Lean formalization

Build it with `cd lean && lake build`. A clean build takes about 11 minutes with 4 threads, using the Mathlib v4.35.0 cache. The project has no `sorry`, no `native_decide` and no `axiom`, and every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

The following are kernel-checked:
- Reidemeister numbers and the four basic lemmas
- The abstract criterion (Theorem 3.1), including the Schur/lattice step and the F4 swap case
- Artin groups as presented groups, with the map to ℤ^T ⋊ Perm T and the equivariant structure of the abelianization of the pure subgroup P
- The finite certificates for H3, F4, H4, E6, E7 and E8
- Out(W/Z) for H3 and F4

Each type theorem takes the cited results as explicit hypotheses instead of assuming them:
- `hW`: W is finite.
- `hCP`: P is characteristic (Cohen–Paris).
- `hBr`: the abelianization of P is free of rank |T| (Brieskorn).
- `hOut`: Out is generated as claimed. This is proved in Lean for H3 and F4. It remains a hypothesis for H4, E6, E7 and E8; for E8 it is proved by hand in the paper.

## Status

The proofs, code and manuscript were developed with substantial AI assistance. They have been reviewed only by AI: an internal audit and an independent "cold referee". No human expert has verified them yet.
