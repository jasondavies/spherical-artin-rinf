# The direct Artin-group argument

This account explains the mathematical route implemented in the Lean development for D5, E6, E7, E8, F4, H3 and H4. The paper proves its Artin-group classification through the stronger crystallographic quotient result. The direct route described here uses the same reflection-lattice and fixed-vector mechanism, with separately certified constituent bases and witnesses, but uses Franzsen–Howlett to control only the holonomy automorphisms induced from Coxeter automorphisms. It does not require the paper's full-holonomy computations.

The [Lean guide](README.md) gives theorem names, build instructions and the precise external hypotheses. References below use the bibliography keys in [the manuscript](../paper/spherical-artin-rinf.tex).

## The Artin-group criterion

Let A be an irreducible spherical Artin group, P its pure subgroup, W its Coxeter group, and T the set of reflections. Conjugation on T gives the faithful action of G = W/Z(W) on the reflection permutation lattice. The affine map sends an Artin generator s to (e_s, s). On P it identifies the abelianisation with 2ℤ^T, equivariantly; dividing by two gives the usual integral permutation module.

Since P is characteristic, an automorphism φ of A induces an integral automorphism M of Pᵃᵇ and an automorphism θ of G, satisfying Mρ(w)M⁻¹ = θ(ρ(w)). Suppose a permutation π of T realises θ. Then N = π⁻¹M commutes with G.

A good constituent means an absolutely irreducible rational constituent U of multiplicity one. Every commuting rational endomorphism restricts to a rational scalar on U. If it and its inverse preserve the lattice, this scalar is ±1. This is the same scalar restriction as in the paper's lattice criterion.

The two witness conditions are:

- **Stable case.** π preserves U, and for each ε = ±1 some h ∈ G makes hπ have eigenvalue ε on U. Since N acts by a sign, hM then has eigenvalue one for an appropriate h.
- **Swap case.** π exchanges two distinct good constituents U₁ and U₂ in both directions. For each ε = ±1 some h makes (hπ)² have eigenvalue ε on U₁. If N has signs ε₁ and ε₂ on these constituents, choose ε = ε₁ε₂. Then (hM)² fixes a nonzero v ∈ U₁, and v + hMv is a nonzero fixed vector of hM because its two summands lie in distinct constituents.

Choose a ∈ A mapping to h. The automorphism ι_aφ has infinitely many twisted classes on Pᵃᵇ because its induced integral matrix hM has eigenvalue one. Projection gives infinitely many classes on P. For an invariant subgroup of finite index, R(ψ|P) ≤ [A:P]R(ψ); hence R(ι_aφ) is infinite. Finally, inner twisting preserves the Reidemeister number, so R(φ) is infinite.

This proves the direct criterion without assuming the quotient classification. `Criterion.lean`, `FreeAbelian.lean`, `Pure.lean` and `Reidemeister.lean` implement these steps.

## The induced-automorphism reduction

Write R(W) for the reflection-preserving automorphism group. A central twist is an automorphism of the form w ↦ wc(w), where c maps W into its centre. Such a twist acts trivially on G. For the seven types, Franzsen–Howlett [FH03, Theorem 31] gives Aut(W) = R(W)𝒜(W), where 𝒜(W) consists of central twists. The published theorem has a proof outline based on involution classes; its decomposition is an explicit external hypothesis of Lean, not a theorem proved by the development.

For E6, E7, E8 and D5, the induced reflection-preserving action is inner. The E6 and odd-D diagram symmetries are induced by the longest element; E7 and E8 have no diagram symmetry. For F4, H3 and H4 there is one further coset, represented by the maps in the paper's witness propositions:

- In F4, the similarity L(x) = (x₁+x₂, x₁−x₂, x₃+x₄, x₃−x₄) exchanges the long and short root lines. It conjugates each reflection to the reflection in its image line. It is non-inner because it exchanges the reflection classes, also after passing to G: two reflections with the same image in G are equal, since the negative of a rank-four reflection is not a reflection.
- In H3, the Galois map followed by the coordinate swap, denoted Σ in the paper, induces the outer automorphism of A5. Its action on the five frames is odd.
- In H4, the icosian map Ψ induces the outer coset described in the witness proposition.

Thus, after an inner adjustment, the induced holonomy automorphism is represented by π = 1 for D5/E6/E7/E8, and by either 1 or the specified outer permutation for F4/H3/H4. An inner adjustment does not change the availability of witnesses, since h ranges over G.

In Lean, the finite part of this reduction is checked by reflection-tuple search certificates rather than assumed from the abstract description of R(W). `FH.lean` proves that the Coxeter decomposition reduces an Artin automorphism to this finite search. Each `Types/XFH.lean` verifies the corresponding certificate and applies the direct criterion.

## Applying the criterion

For E6, E7 and E8, the root-line graph provides good nontrivial constituents. The identity supplies the positive sign, and a reflection supplies the negative sign. All reflections are conjugate; if every reflection acted trivially, the constituent would be trivial.

For D5, use the ten-dimensional constituent U⁻ spanned by the differences of the two lines e_i ± e_j. Its weight argument proves absolute irreducibility and multiplicity one. The identity and a reflection supply the two signs, and only the inner holonomy coset occurs.

For H3 and H4, the inner coset is handled by the same reflection argument. The frame constituent of H3 and the matrix-coefficient constituent of H4 are preserved by their respective outer permutations. The explicit witnesses in the paper supply both signs in each outer coset.

For F4, the long and short frame constituents are distinct good two-dimensional constituents. In the inner coset, the identity and a long reflection give both signs on the long constituent. In the outer coset, π_L exchanges the two constituents, π_L² = 1 supplies the positive square witness, and (sπ_L)² for a long simple reflection s supplies the negative square witness. The swap case applies.

These are the seven conditional Artin-group theorems. Their hypotheses are finiteness of W, characteristicity of P [CP03], the abstract rank statement Pᵃᵇ ≅ ℤ^|T| [Bri71], and the Coxeter automorphism decomposition [FH03]. The equivariant lattice identification and finite witnesses are checked in Lean. The full quotient classification is outside this development. A separate `Dihedral5` development proves the I₂(5) affine automorphism and Reidemeister count 18, with the identification of the affine model with the presented quotient left explicit; see [the Lean guide](README.md).

## The D5 attribution

Paris–Soroko [PS26, Lemma 4] proves that the kernel of the natural epimorphism A[D5] → A[A4], obtained by identifying the two terminal generators, is fully characteristic. Every automorphism therefore descends to the braid-group quotient A[A4], which has R∞. The surjection on twisted conjugacy classes gives R∞ for A[D5]. This is a deduction from their lemma, not a theorem stated in their paper.

This deduction is distinct from the formalised Franzsen–Howlett proof. [SV24] states its D_n theorem for n ≥ 6 and leaves D5 as a conjecture. The paper includes an independent D5 proof within its uniform quotient argument without claiming priority for that case.
