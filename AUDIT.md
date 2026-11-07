# Proof and source audit

Audit date: 7 November 2026. This records the current argument and its verification scope. It is an AI audit; no human expert review has been recorded.

## Dependency structure

Theorem B is the main mathematical route. The translation-lattice proposition identifies the actual crystallographic group. The fixed-vector criterion reduces positive cases to rational constituents and holonomy witnesses. The exceptional cases use exact certificates, the classical families use uniform character arguments, and the dihedral theorem treats all parameters explicitly. Theorem A follows from characteristicity of [P,P], the quotient inequality for Reidemeister numbers, and the known dihedral Artin-group result. Proposition C independently counts the classes of one finite-Reidemeister automorphism.

The [direct Artin proof](lean/DIRECT_PROOF.md) beside the Lean sources treats seven cases through Franzsen–Howlett. Appendix C only summarises its scope and dependencies. This is the route covered by the conditional Lean theorems. The main proof of Theorem B does not depend on that decomposition.

## Mathematical audit

| Obligation | Argument checked | Verification boundary |
|---|---|---|
| Actual affine quotient and translation lattice | The affine map has kernel [P,P]. The preimage of Z(W) acts faithfully by translations: its coordinates are even over 1 and odd over −I. Thus L = 2ℤ^T, enlarged by ℤ𝟙 exactly when the centre is nontrivial. Faithful finite holonomy and the full lattice give discreteness and cocompactness. | Uses the arrangement-complement identification and Marin's crystallographic theorem; the meridian argument for H₁ is included. |
| Characteristicity of L | Any abelian normal subgroup of finite index centralises its intersection with L, so its linear parts fix a full lattice and are trivial. | Applies with torsion. |
| Scalar signs and swaps | A commuting integral automorphism acts as a rational scalar on a good constituent; it and its inverse preserve the constituent lattice, forcing ±1. In the swap case both directions of interchange are stated, and v+gDv is nonzero in a direct sum of distinct constituents. | Absolute irreducibility and multiplicity one are essential. Rational irreducibility alone does not suffice. |
| B_n/D_n reflection preservation | For signed involutions (a,b,c), fixed-line counts are a(a−1)+b(b−1)+2c in D and a²+b²+2c in B. Lifts squaring to −I fix no real line. Solving the reflection-character equations uniformly leaves only reflections and two extra kinds. | Algebraic inequalities cover every rank; bounded checks only corroborate them. |
| Class-size exclusions | The B6 diagonal (3,3,0) class has quotient size 10 rather than 30. The D_n two-negative-coordinate class has size C(n,2), rather than n(n−1). Neither D class splits on restricting to even signed permutations: an unused fixed coordinate supplies an odd centraliser element. Central quotienting does not halve these D class sizes for n ≥ 5. | The restriction and central-quotient steps are separately justified; direct conjugacy-orbit checks cover B6 and D5–D12. |
| Root-isometry reduction | Orders of products of reflections survive quotienting by ±I because the product fixes a nonzero complement. Signs can be chosen along the diagram tree to recover the simple-root Gram matrix. The resulting isometry normalises W. For B_n it preserves root lengths and is a signed permutation; for D_n it is inner up to a diagram symmetry. | No lifting assumption for an arbitrary holonomy automorphism. |
| D4 | The sign-fixed module has dimensions 1,3,2. The other sign weights have orbit size three, so no other degree-two rational constituent occurs. The degree-two holonomy image is S3; its integral normaliser acts as ±S3. | Avoids the reducible U⁻ as a purported good constituent. |
| Odd dihedral m divisible by 3 | The rational rotation decomposition has U_d ≅ ℚ(ζ_d), d dividing m. The unique rational degree-two constituent is U₃, with image S3. | Distinguishes rational constituents from their complex splittings. |
| Dihedral 4 dividing m | The two nontrivial rational character lines occur once, with opposite values on S. Normalisers preserve or exchange them. In the exchanged case D² is a common scalar ±1, and choosing g = 1 or S makes (gD)² = 1. | Includes m = 4 and the enlarged translation lattice. |
| Odd dihedral m not divisible by 3 | D = I−C−C⁻¹ has determinant −1 by (I+C)(I−C+C²)=I+C³. With d=e₀+e₁, generator corrections are −2e_(m−1), −2e₂. The only eigenvalue of modulus one is −1 on the constant line; no gD has eigenvalue one. | Checks lattice and extension, not merely ambient affine conjugation. No exact general-m Reidemeister number is asserted. |
| Dihedral m ≡ 2 modulo 4 | Pair even j with j+m/2 and apply the block [[1,2],[2,5]]. The pairing is G-equivariant; D and its inverse preserve L and the extension. Eigenvalues 3±2√2 avoid the unit circle. | Works for every such m ≥ 3. |
| I₂(5) exact count | Ten adjusted determinants are nonzero. Four conjugacy fibres have cyclic quotients of orders 2,22,22,10 and centraliser orbit counts 1,6,6,5. Independent enumeration of all 140 translation-twisted classes gives 13 orbits of size ten and five of size two. | R=18. Torsion is exhibited explicitly; the determinant average 14 is not used as a Reidemeister formula. |
| Odd-dimensional alternative | The unique good constituents of degrees 5,15,27,35,25 for D5,E6,E7,E8,H4 have finite integral normaliser: its kernel in Aut(image) is ±I. Hiss–Lutowski then gives a holonomy-adjusted fixed vector. | The torsion-free DDP conclusion is not applied directly to these quotients; the crystallographic determinant criterion is used. This particular route does not supply F4/H3. |

The audit found no obstruction to the stated classification. It tightened the interchange hypothesis, the class-size justifications, the rational dihedral decomposition and the separation of the two proof routes. This conclusion is not a substitute for human verification of the proofs.

## Primary-source checks

The table records specific mathematical inputs, not a claim to an exhaustive priority search.

| Source and location | Use in the paper |
|---|---|
| [Cohen–Paris, Theorem 1.4](https://arxiv.org/pdf/math/0204242); Proposition 5.4, Corollary 5.5 and the cited classical lemmas | P is characteristic. Their GAP-assisted calculations are cited inputs and have not been rerun here. |
| Brieskorn, *Inventiones* 12 (1971), 57–61 | Identifies P with the fundamental group of the reflection-arrangement complement. The required first-homology computation is proved directly using meridians and winding numbers. |
| [Marin, Theorem 2.1 and Corollary 2.2](https://arxiv.org/pdf/1509.06213) | A/[P,P] is crystallographic with holonomy W/Z(W), also when the Coxeter centre is nontrivial. |
| [Humphreys, §1.8 p. 15 and Theorem 1.12(c),(d), pp. 22–23](https://sites.math.washington.edu/~billey/classes/reflection.groups/references/Humphreys.ReflectionGroupsAndCoxeterGroups.pdf) | Simple transitivity on simple systems and pointwise stabilisers generated by perpendicular reflections. Locations checked in the scanned text. |
| [Carter, Lemma 5, p. 5](https://www.numdam.org/item/CM_1972__25_1_1_0.pdf) | Decomposition of a Weyl-group involution into orthogonal reflections, used in the E8 holonomy proof. |
| [Franzsen–Howlett, Theorem 31](https://www.maths.usyd.edu.au/u/bobh/fh02.pdf), published pp. 329–330; Theorem 18 and Corollary 19 | Alternative Artin proof only. Theorem 31 is presented with a proof outline; no claim of a fully reproduced classification proof is made. |
| [Dekimpe–De Rock–Penninckx, Theorem 4.7, pp. 363–364](https://www.tmna.ncu.pl/static/files/v34n2-10.pdf) | The integral subrepresentation, image non-conjugacy and normaliser-eigenvalue hypotheses are explicit. The manifold theorem assumes torsion-freeness. |
| [Dekimpe–Kaiser–Tertooy, Theorem 3.3, Theorem 3.4 and Algorithm 1](https://arxiv.org/pdf/1709.07649) | The determinant test applies to crystallographic groups with torsion. The averaging formula requires a Bieberbach group. Algorithm 1 tests affine extension compatibility. Theorem 3.3 credits Dekimpe–Penninckx, Corollary 3.10. |
| [Hiss–Lutowski I, Definition 1.1.3 and Theorem 1.1.5](https://arxiv.org/pdf/2504.04978), with [Part II](https://arxiv.org/html/2601.09622v1) | Requires a nontrivial irreducible real representation of odd degree and a finite-order normalising operator. The paper proves that last hypothesis for the relevant integral normalisers. |
| [Calvez–Soroko, Theorem 1 and its dihedral proof](https://arxiv.org/pdf/2106.13260) | Supplies R∞ for dihedral Artin groups, including the parameters with negative crystallographic quotients. |
| [Dekimpe–Gonçalves–Ocampo, Theorems 28, 31 and the proof of Corollary 32](https://arxiv.org/pdf/2403.12528); [journal metadata](https://arxiv.org/abs/2403.12528) | R∞ for the virtual-braid quotients with three and four strings. Published in Journal of Algebra 663 (2025), 20–47, DOI 10.1016/j.jalgebra.2024.09.002; the bibliography gives this publication. |
| [Gonçalves–Guaschi–Ocampo, §5](https://arxiv.org/pdf/1503.04527), and [Dekimpe–Kaiser–Tertooy, Table 2](https://arxiv.org/pdf/1709.07649) | The A2 quotient is IT 161; the complete three-dimensional negative list omits it. Its positive result is acknowledged as implicit in these sources. |
| [Ocampo, §1](https://arxiv.org/html/2610.20478v1); [Leite–Ocampo–Santos Júnior–Teixeira](https://arxiv.org/html/2610.33308v1) | Related torus-bundle and framed-braid quotient work, distinguished by the groups and questions studied. |

For D5, [Soroko–Vaskou, Theorem 1 and §1](https://arxiv.org/html/2409.18123v2) cover n ≥ 6 and explicitly leave n = 5 open. [Paris–Soroko, Theorem 1](https://arxiv.org/html/2606.26082v2) give Aut(A[D5]) = Inn ⋊ ⟨inversion⟩; the paper records the short R∞ deduction without attributing that statement to their theorem. [Soroko, §1](https://arxiv.org/html/2610.13904v1) lists n ≥ 5 with a reference to Soroko–Vaskou. These statements have been checked directly; they do not justify a priority claim for D5.

## Certificate failure checks

A positive computation must establish that all required objects were found. The auxiliary outer-witness checker now requires the full dimension multiset and both signs for every constituent, rejects duplicate or missing witnesses, and verifies scalar commutants and stable/swap images exactly. The scalar checker requires the exact requested dimensions, nontrivial reflection action and both F4 constituents. The independent commutant checker requires its complete expected eigenspace decomposition. Positive uniform checks require nonempty constituent and automorphism lists. Empty command lines are rejected by the scripts that require explicit types.

`code/test_certificate_guards.py` injects empty and partial data into these paths, including the actual outer-checker entry point and the E8 commutant calculation. It also exercises the command-line exit codes. These regression checks are part of the one-command verification workflow; passing runs on intact data alone would not establish that omissions are rejected.

## Reproduction and remaining work

`python3 scripts/verify.py --clean` is the complete verification command after dependency setup. It runs eleven Python verification jobs, builds the PDF with resolved references and no overfull boxes, rebuilds the Lean package while retaining the Mathlib cache, and checks the axiom report. Logs and JSON summaries are generated in `verification/`; they are reproducible build outputs rather than source files.

The final full workflow passes all eleven Python jobs, including eight certificate-failure regression tests, every m from 3 through 46, direct conjugacy orbits in B6 and D5–D12, and the two independent R=18 counts. The 17-page PDF builds with resolved references and no overfull boxes. Project Lean outputs were cleaned and rebuilt; the final source-tree build and axiom report both pass. The reported axioms are only `propext`, `Classical.choice` and `Quot.sound`. Lean definitions and proof terms are unchanged; source edits update documentation. The final commands, timings and outcomes are recorded in `verification/all-summary.json`.

Before submission, the authors still need to supply names, affiliations and a contribution statement, obtain a human mathematical review, and refresh the priority/bibliography check. No new Lean theorem for Theorem B or Proposition C is claimed.
