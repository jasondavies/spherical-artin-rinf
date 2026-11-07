# Property R∞ for the exceptional spherical Artin groups

This repository proves property R∞ for the Artin groups of types E6, E7, E8, F4, H3 and H4. Property R∞ means that every automorphism has infinitely many twisted conjugacy classes. The proof does not require determining Aut(A).

Combined with earlier work, the result shows that every irreducible spherical Artin group of rank at least 2 has R∞. This settles the spherical case of AIM problem list "Geometry of Artin groups", Problem 8.6.

## Contents

| Path | What it holds |
|---|---|
| `paper/` | Manuscript (`main.tex`, `main.pdf`) |
| `code/` | Computational certificates and independent checkers. See `code/README.md` for commands and expected output. |
| `lean/` | Lean 4 / Mathlib formalization (in progress). See `lean/README.md`. |
| `AUDIT.md` | Claim-by-claim audit and the open items |
| `REVIEWER_NOTE.md` | One-page note for reviewers |
| `provenance/` | Earlier draft and the internal referee summary |

## Status

The proofs, code and manuscript were developed with substantial AI assistance. They have been reviewed only by AI: an internal audit and an independent "cold referee". No human expert has verified them yet.
