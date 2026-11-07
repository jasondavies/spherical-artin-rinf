# Note for an external reviewer (geometric group theory)

**Provenance.** This is AI-assisted work (Anthropic's Claude and OpenAI's Codex): the argument, code, Lean formalisation and manuscript.
It has been reviewed only by AI systems:
- an internal audit;
- two internal AI "cold referee" rounds;
- external AI reviews, including manuscript-only reviews, a review of the Python and Lean sources, and the latest
  quotient-focused review.

The tables in AUDIT.md list every review point, whether it was confirmed or refuted, and how it was handled. None of
this is journal peer review, and no human expert has checked the work. We are asking you to be that check.

**Claim.** The Artin groups of spherical types D5, E6, E7, E8, F4, H3 and H4 have property R∞. Combined with
Calvez–Soroko (A_n, B_n, D4, I2(m)) and Soroko–Vaskou (D_n, n ≥ 6), every irreducible spherical Artin group of
rank ≥ 2 then has R∞.

**About D5.**
- Soroko–Vaskou (arXiv:2409.18123v2) leave D5 open as a conjecture.
- Paris–Soroko (arXiv:2606.26082) compute Aut(A[D5]) = Inn ⋊ ⟨inversion⟩. R∞ follows from this in a few lines
  (Remark 5.3), but they do not state it.
- Soroko (arXiv:2610.13904, §1) lists D5, attributing it to Soroko–Vaskou.

Our method gives an independent proof (Prop 5.2). Please check the attribution.

**Theorem B.** A/[P,P] has R∞ for the same seven types. The proof is now in §6.2 and uses the full
Aut(W/Z) statements of Appendix B, not only Franzsen–Howlett.

**Proposition C.** A(I₂(5))/[P,P] admits an automorphism with **R = 18**. This confirms failure of R∞ for the quotient while correcting the exploratory claim R = 14. The script behind that claim used the Bieberbach determinant average on a group with torsion. Section 6.5 gives the matrix, translation, extension check, ten nonzero determinants, and a direct class count. The independent exact checker `code/indep/dihedral_quotient.py` confirms the count by both centralizer orbits and enumeration of all 140 translation-twisted classes. The general-m exploratory script has not been certified.

**Alternative proof.** Section 6.3 verifies the odd-dimensional route for D5, E6, E7, E8 and H4, using unique good constituents of dimensions 5, 15, 27, 35 and 25. It proves the required normalisers are finite and uses the determinant criterion for crystallographic groups with torsion. This avoids applying a flat-manifold theorem outside its hypotheses. The explicit witnesses also cover F4 and H3, where this particular route does not apply. Dekimpe–Gonçalves–Ocampo (2024), Theorems 28 and 31, is now cited for the distinct virtual-braid quotients with three and four strings.

**Novelty and precedents.**
- New:
  - the Artin-group application via the characteristic reflection lattice H₁(P) ≅ ℤ^T;
  - controlling the finite symmetry by Aut(W) (Franzsen–Howlett) instead of Aut(A);
  - explicit sign and swap witnesses;
  - the exceptional cases.
- Precedents for "eigenvalue one via representation theory":
  - Dekimpe–Gonçalves–Ocampo;
  - Dekimpe–De Rock–Penninckx, Thm 4.7;
  - Dekimpe–Penninckx / Dekimpe–Kaiser–Tertooy, Thm 3.3;
  - Hiss–Lutowski, Parts I and II (arXiv:2504.04978, 2601.09622).
- A/[P,P] is crystallographic with holonomy W/Z(W), by Marin, Thm 2.1.

**Argument.**
1. P = ker(A → W) is characteristic (Cohen–Paris Thm 1.4). For these types that proof is GAP-assisted, and we have
   not re-run it.
2. f: A → ℤ^T ⋊ W gives H₁(P) ≅ ℤ^T as a permutation module.
3. Thm 3.3: φ acts as πN, and N = ±1 on a good constituent. Witnesses then give a fixed vector for φ′ = ι_a∘φ.
4. Lemma 4.1 (Franzsen–Howlett, Adv. Geom. 3 (2003), Thm 31, pp. 329–330; its proof there is an outline).
   Modulo inner automorphisms, the induced automorphisms of W/Z are:
   - trivial for E_n and B_n;
   - graph automorphisms for D_n and F4;
   - one extra class for H3 and H4.
5. Explicit good constituents:
   - SRG eigenspaces for E_n;
   - frame modules for H3 and F4;
   - End(V) in the icosian model for H4.

**What to check (in order).**
1. Proposition C (§6.5): the actual extension and the torsion-sensitive class count.
2. Theorem B (§6.2), including the full holonomy-automorphism certificates in Appendix B.
3. The odd-dimensional alternative (§6.3) and extension-compatibility criterion (§6.4).
4. Thm 3.3, case (ii), and Prop 2.4.
5. Lemma 4.1, the quotation of Franzsen–Howlett, and Props 4.2–4.6 with their finite certificates.
6. Prop 5.2 and Remark 5.3 (D5).

**Literature questions.**
- Is R∞ for E6–E8, F4, H3 or H4, or for A/[P,P], known or announced?
- Is there a complete published proof of Franzsen–Howlett Thm 31?
- Has D5 been proved anywhere?
- What are the exact section numbers for the cited textbook facts (Humphreys, Orlik–Terao)?

**Formal verification** (`lean/`, as of commit 296176a).
- The new quotient results and Proposition C are not Lean-formalised.
- The kernel checks the criterion and the finite certificates for **all seven types** D5, E6, E7, E8, F4, H3 and H4.
- No `sorry`, no `axiom`, no `native_decide`.
- Each final theorem `artin_X_R_infty_FH` has exactly four hypotheses: `hW` (W finite), `hCP` (Cohen–Paris),
  `hBr` (P^ab ≅ ℤ^N as groups, N = |T|) and `hFH` (Franzsen–Howlett Thm 31).
- The older `hOut` hypothesis is **no longer needed**. It survives only in legacy theorems, and is proved there for
  H3 and F4.
- The Lean development uses computer-found constituents, not the hand constructions of §4.

**Reproduce** (Python 3 + numpy + sympy; see `code/README.md`). Every certificate script exits with a nonzero status
if an expected value fails:
```
cd code/indep
python3 dihedral_quotient.py          # actual I2(5) extension, determinants, torsion, two exact R = 18 counts
python3 explicit_constituents.py      # proof certificates for §4.2, Lemma 4.5, Prop 4.6, §5 (exact; asserts)
python3 referee_v3_E.py               # E types (exact ranks; asserts)
python3 indep_check.py H3 F4 H4 E6 E7 && python3 out_check.py H3 F4 H4 D5 E6 E7 && python3 out_check_stab.py E7 E8
cd .. && python3 certify.py H3 F4 H4 E6 E7 E8 D5 && python3 certify_outer.py H3 F4 H4
```
