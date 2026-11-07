# Note for an external reviewer (geometric group theory)

**Provenance.** AI-assisted work (Anthropic's Claude): argument, code, Lean formalisation and manuscript. It has been
reviewed only by AI systems:
- an internal audit;
- an AI "cold referee" (minor revision, no errors found);
- an external AI review of the manuscript, which found two genuine errors (both fixed);
- a second internal AI cold referee round (minor revision), which found that **D5 is not in the literature**.

See the tables in AUDIT.md.

None of this is journal peer review, and no human expert has checked it. We are asking you to be that check.

**Claim.** The Artin groups of spherical types **D5**, E6, E7, E8, F4, H3 and H4 have property R∞. With Calvez–Soroko
(A_n, B_n, D4, I2(m)) and Soroko–Vaskou (D_n, n ≥ 6), every irreducible spherical Artin group of rank ≥ 2 then has R∞.

**D5.** Soroko–Vaskou (arXiv:2409.18123v2) prove only n ≥ 6 and conjecture D5. Paris–Soroko (arXiv:2606.26082)
compute Aut(A[D5]) = Inn ⋊ ⟨inversion⟩ but never state R∞. Soroko (arXiv:2610.13904, §1) lists D_n, n ≥ 5, as
proved in Soroko–Vaskou, which we believe is a misattribution. We give two proofs:
- our Prop 5.2;
- a near-immediate deduction from Paris–Soroko Thm 1, Remark 5.6(b) and Lemma 2.1(c), which we did not find written
  down.

Please check this attribution question in particular.

**Novelty.**
- New: the D5 case; the Artin-group application through the characteristic reflection lattice H₁(P) ≅ ℤ^T, the use of Aut(W)
  (Franzsen–Howlett) instead of Aut(A), the explicit sign and swap witnesses, and the exceptional cases.
- Precedents for "eigenvalue one via representation theory": Dekimpe–Gonçalves–Ocampo (pure braids),
  Dekimpe–De Rock–Penninckx Thm 4.7 (flat manifolds), the determinant criterion of Dekimpe–Kaiser–Tertooy Thm 3.3,
  and Hiss–Lutowski.
- A_n, B_n and D_n are re-proved uniformly as a demonstration. Apart from D5, these cases are known.

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
5. Prop 5.2 and Remark 5.3 (D5); Prop 5.4 (the D4 correction).
6. Remark 5.5 (dihedral types: odd m only).

**Literature questions.**
- Is R∞ for E6–E8, F4, H3 or H4 known or announced?
- Is the journal version of Franzsen–Howlett Thm 31 identical to the preprint statement we read? Is there a complete
  published proof?
- Has D5 been proved anywhere (perhaps in a journal version of Soroko–Vaskou)?
- Exact section numbers for the textbook facts we cite (Humphreys, Orlik–Terao).

**Formal verification.** `lean/` checks the criterion and the finite certificates in the Lean kernel, with no sorry,
no axiom and no native_decide. Its hypotheses are W finite, Cohen–Paris, Brieskorn (`hBr`: P^ab ≅ ℤ^N as groups, N = |T|), and `hOut`.
D5 is not formalised. `hOut` is proved
in Lean for H3 and F4 and remains a hypothesis for H4, E6, E7 and E8. The Lean development uses the v2 numbering.

**Reproduce** (Python 3 + numpy + sympy; see `code/README.md`):
```
cd code/indep
python3 explicit_constituents.py                  # all explicit constructions of paper v3 (~22 s)
python3 referee_v3_E.py && python3 referee_v3_H4.py && python3 referee_v3_DFH3.py   # internal v3 AI referee's checkers
python3 indep_check.py H3 F4 H4 E6 E7 && python3 out_check.py H3 F4 H4 E6 E7
cd .. && python3 certify.py H3 F4 H4 E6 E7 E8 && python3 certify_outer.py H3 F4 H4
```
