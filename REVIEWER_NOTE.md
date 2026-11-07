# Note for an external reviewer (geometric group theory)

**Provenance.** AI-assisted work (Anthropic's Claude): argument, code, Lean formalisation and manuscript. It has been
reviewed only by AI systems:
- an internal audit;
- an AI "cold referee" (minor revision, no errors found);
- an external AI review of the manuscript, which found two genuine errors. Both are fixed; see the table in
  AUDIT.md.

None of this is journal peer review, and no human expert has checked it. We are asking you to be that check.

**Claim.** The Artin groups of spherical types E6, E7, E8, F4, H3 and H4 have property R∞. With Calvez–Soroko and
Soroko–Vaskou (and Soroko 2026 for D5), every irreducible spherical Artin group of rank ≥ 2 then has R∞.

**Novelty.**
- New: the Artin-group application through the characteristic reflection lattice H₁(P) ≅ ℤ^T, the use of Aut(W)
  (Franzsen–Howlett) instead of Aut(A), the explicit sign and swap witnesses, and the exceptional cases.
- Precedents for "eigenvalue one via representation theory": Dekimpe–Gonçalves–Ocampo (pure braids),
  Dekimpe–De Rock–Penninckx Thm 4.7 (flat manifolds), the determinant criterion of Dekimpe–Kaiser–Tertooy Thm 3.3,
  and Hiss–Lutowski.
- A_n, B_n and D_n are re-proved uniformly as a demonstration; these cases are known.

**Argument (paper v3).**
1. P = ker(A → W) is characteristic (Cohen–Paris Thm 1.4). For our types, Cohen–Paris is GAP-assisted (their §5);
   we have not re-run those computations.
2. f: A → ℤ^T ⋊ W gives H₁(P) ≅ ℤ^T as a permutation module.
3. Thm 3.3: φ acts as πN, where N commutes with W, and N = ±1 on a good constituent. A stable or swap witness then
   gives a fixed vector for some inner twist φ′. Hence R(φ′|_P) = ∞, so R(φ′) = ∞, and R(φ) = R(φ′).
4. Lemma 4.1 (Franzsen–Howlett Thm 31): modulo inner automorphisms, the induced automorphisms of W/Z are:
   - trivial for E_n and B_n;
   - graph automorphisms for D_n and F4;
   - one extra class for H3 and H4.
5. Explicit good constituents:
   - SRG eigenspaces for E_n, with a hand proof of the three orbitals via perpendicular subsystems;
   - frame modules for H3 and F4;
   - End(V) matrix coefficients in the icosian model for H4.

**What to check (in order).**
1. Thm 3.3 (case ii).
2. Prop 2.4.
3. Lemma 4.1, and whether Franzsen–Howlett Thm 31 is correctly quoted. We read the authors' preprint, and its proof
   there is an outline. For the exceptional types Appendix B gives independent control.
4. Props 4.2–4.6 and Lemma 4.5.
5. Props 5.2 and 5.3 (the D4 correction).
6. Remark 5.4 (dihedral types: odd m only).

**Literature questions.**
- Is R∞ for E6–E8, F4, H3 or H4 known or announced?
- Is the journal version of Franzsen–Howlett Thm 31 identical to the preprint statement we read? Is there a complete
  published proof?
- Is the attribution for D5 correct?
- Exact section numbers for the textbook facts we cite (Humphreys, Orlik–Terao).

**Formal verification.** `lean/` checks the criterion and the finite certificates in the Lean kernel, with no sorry,
no axiom and no native_decide. Its hypotheses are W finite, Cohen–Paris, Brieskorn rank, and `hOut`. `hOut` is proved
in Lean for H3 and F4 and remains a hypothesis for H4, E6, E7 and E8. The Lean development uses the v2 numbering.

**Reproduce** (Python 3 + numpy + sympy; see `code/README.md`):
```
cd code/indep
python3 explicit_constituents.py                  # all explicit constructions of paper v3 (~22 s)
python3 indep_check.py H3 F4 H4 E6 E7 && python3 out_check.py H3 F4 H4 E6 E7
cd .. && python3 certify.py H3 F4 H4 E6 E7 E8 && python3 certify_outer.py H3 F4 H4
```
