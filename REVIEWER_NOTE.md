# Note for a mathematical reviewer

The main result is a classification of property R∞ for Γ_X = A(X)/[P,P], where X is irreducible spherical of rank at least two. All ranks at least three are positive. For I₂(m), the positive parameters are exactly 4 | m or m odd with 3 | m. This implies the corresponding Artin-group result; the remaining dihedral Artin cases are known. An explicit automorphism for I₂(5) has R = 18.

The paper and supporting code were developed with substantial AI assistance. The current audit is an AI mathematical and computational audit, not independent human peer review. [AUDIT.md](AUDIT.md) records the proof dependencies and source checks.

## Suggested reading order

1. **Translation lattice and fixed-vector criterion.** Check the lattice 2ℤ^T, enlarged by ℤ𝟙 when the Coxeter centre is nontrivial; its characteristicity; and the stable/swap argument. The swap hypothesis explicitly exchanges both constituents.
2. **Uniform classical proof.** Check the signed-involution character equations, the B6 and D_n class-size exclusions, and the root-isometry reduction. Only character-preserving holonomy automorphisms need be controlled. D4 uses its unique rational degree-two frame constituent.
3. **All four dihedral cases.** Check the rational degree-two constituent for odd multiples of three, the two character lines for multiples of four, and the actual extension compatibility of both negative families. These are uniform proofs, not extrapolations from finite searches.
4. **The I₂(5) count.** Check the cyclic quotient coordinates and centraliser actions, giving 1 + 6 + 6 + 5 = 18. The group has torsion, so the Bieberbach determinant average does not compute its Reidemeister number.
5. **Exceptional proof inputs.** Check the explicit constituents and Appendix B's full holonomy automorphism certificates, including the hand proof for E8. D5 is covered by the uniform classical proof; its separate full-holonomy computation is optional corroboration. The Hiss–Lutowski comparison applies to D5/E6/E7/E8/H4 through odd-dimensional constituents; the proof establishes finiteness of their integral normalisers and uses the determinant criterion valid with torsion.

## Attribution and formal scope

D5 also follows from Paris–Soroko, Lemma 4: the natural map to A[A4] has fully characteristic kernel, so the known braid-group result and the quotient inequality imply R∞. This is a deduction from their lemma. The paper gives an independent uniform proof without claiming priority for D5. The virtual-braid quotient results of Dekimpe–Gonçalves–Ocampo are acknowledged separately from these spherical quotients. The A2 quotient is already implicit in the earlier space-group classification.

Appendix C summarises the dependencies of the direct Artin-group route formalised in Lean; its complete account is in [the accompanying documentation](lean/DIRECT_PROOF.md). Its seven main theorems assume finiteness of W, characteristicity of P, the rank of P's abelianisation and the Franzsen–Howlett decomposition. H3 and F4 also have theorems avoiding the latter assumption. Lean also proves Proposition C for the presented Artin quotient: a Schreier calculation proves the affine map has kernel [P,P], and the exact R = 18 result transfers through the resulting isomorphism. There are no external mathematical hypotheses in this theorem. The full quotient classification remains outside Lean.

## Reproduction

After the setup in [README.md](README.md), run `python3 scripts/verify.py --clean`. The [code guide](code/README.md) maps scripts to proof obligations; the [Lean guide](lean/README.md) specifies hypotheses. Fresh logs are generated in `verification/`.

The matching source-and-code archive is produced by `python3 scripts/package_review.py` after a successful full verification run. It includes the PDF, supplementary proof account, checkers, dependency pins, current logs and a checksum manifest, so the implementation and the manuscript can be reviewed together.

The remaining external checks are a human mathematical review and a final priority/bibliography check close to submission. The paper names Jason Davies as author and includes an AI transparency statement and disclosure.
