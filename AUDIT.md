# AUDIT: Twisted conjugacy in irreducible spherical Artin groups (R∞ for D5, E6, E7, E8, F4, H3, H4)

Auditor: AI (Claude). No human expert has checked this. Newest section first.

## v3.1: internal v3 AI cold referee (minor revision) → how handled

The referee found no mathematical error and confirmed every explicit constituent and witness with their own code.
That code is now in `code/indep/referee_v3_*.py`, with logs in `code/logs/referee_v3_*.log`.

### The main finding: D5 is not in the literature

I checked the referee's reading myself, in the arXiv texts.

* **SV24 = arXiv:2409.18123v2** (7 Feb 2026). §1, Theorem 1: "Let n ⩾ 6. Then the Artin group A[Dn] and its central quotient A[Dn]/Z(A[Dn]) have property R∞." A little later: "The only remaining case in the family A[Dn] is A[D5]. At present we do not have a description of Aut(A[D5]), which is the key input in our approach; we conjecture though that both A[D5] and A[D5]/Z(A[D5]) have property R∞ as well." **Confirmed: n ≥ 6 only, and D5 is conjectured.**
* **PS26 = arXiv:2606.26082v2.** Theorem 1: "Let A = A[D5] and C2 = Z/2Z. Then Aut(A) = Inn(A) ⋊ ⟨χ⟩ ≃ A/Z(A) ⋊ C2. In particular, Out(A) ≃ C2", where χ is the inversion t_i ↦ t_i⁻¹. A full-text search for "R∞", "twisted" and "Reidemeister" finds **no occurrence**. **Confirmed: Aut is computed, R∞ is never stated.**
* **Sor26 = arXiv:2610.13904v1, §1.** It lists "spherical groups of type Dn, n ⩾ 5, in [SV24]". This **misattributes** D5, given the two items above. Its own theorems concern non-spherical groups only (abstract: "every length-preserving automorphism of a nonspherical Artin or Coxeter group").

**How it is handled.** D5 is now claimed as part of the Main Theorem: in the abstract, the introduction, the Main Theorem statement, the Corollary proof, §5 and the new Remark 5.3. Two routes are given:

1. Prop 5.2 with n = 5. This uses Cohen–Paris, Franzsen–Howlett Thm 31(3) (Aut(W(D5)) = R(W) ≅ W), and the weight argument. The exact checks (D5: U⁻ good, negating e_5 gives dimensions (6,4)) are in `explicit_constituents.log` and `referee_v3_DFH3.log`.
2. PS26 Thm 1 + the inversion remark (Remark 5.6(b)) + R(id) = ∞ (A^ab ≅ ℤ) + Lemma 2.1(c). This is presented honestly as a near-immediate deduction that, as far as we can tell, nobody has written down.

Sor26 is no longer cited for any spherical case. Its misattribution is noted politely in the introduction.

### Minor items

| # | Referee point | How handled |
|---|---|---|
| 1 | Main Theorem proof: treat the F4 inner class explicitly; say how H3 and H4 inner are covered | Done. F4 inner uses π = 1, U = U_long, with witnesses h = 1 and a long reflection (Prop 4.4(b)). H3/H4 inner use Remark 3.5 (reflections conjugate, U nontrivial). D5 is added as a bullet. |
| 2 | Lemma 3.2(i): rule out U meeting two isotypic components; U stable under the orbital matrices | Done. The proof now uses central idempotents, then U_ℂ = V_i ⊗ L, then m_i = 1. |
| 3 | Prop 4.6(c): spell out the steps | Done, in three steps: π ∈ ρ(W)π_Ψ; π_Ψ = ψ is outer in Aut(K); Aut(A5) = S5, so composing with an inner conjugation gives conjugation by a transposition δ. Notation: λ_V for the representation of V, Ω for the rotation. |
| 4 | Prop B.2: 6-root line; Carter Lemma 5 numbering | Done. **Carter's numbering verified** in the Numdam scan of Compositio Math. 25 (1972) 1–59: "LEMMA 5. Every involution w in W can be expressed as a product of l(w) reflections corresponding to mutually orthogonal roots." |
| 5 | Lemma B.1: Φ irreducible; Aut(Φ) = W⋊Gr; orders of products in W/Z | Done. |
| 6 | Lemma 4.1: circular last sentence | Replaced by "θ_r(ρ(T)) = ρ(T) for r ∈ R(W), by definition of R(W)". |
| 7 | Prop 4.2: reference for the perpendicular subsystems | Not done as asked: I could not verify a specific table reference. The paper instead proves the identification. Each (number of roots, rank) pair in the table occurs for exactly one simply-laced root system of that rank, and the counts and ranks are machine-checked. It also notes that these are the classical centraliser facts. |
| 8 | FH03: outline, typo, published theorem number | Done. The paper says the proof of Thm 31 is an outline based on involution class sizes, and points to Appendix B for corroboration. It notes the typo α_χ → α_ζ in item (9). **The published theorem number could not be verified**: the journal PDF was not accessible. The bibliography says we cite the preprint numbering and gives its URL. |
| 9 | Position Thm 3.3 relative to DP11/DKT19/DDP09; f(A) is not strictly crystallographic when Z(W) ≠ 1 | Done. New Remark 3.4. DP11 is added to the bibliography (JFPTA 9 (2011) 257–283, as cited in DKT19). The DDP09 summary now includes its uniqueness-of-image hypothesis, which implies multiplicity one. |
| 10 | Lean paragraph: hBr is P^ab ≅ ℤ^N | Done. The paper also says D5 is not formalised. |
| 11 | Notation clashes (P, f, ρ, φ) | Done: rotation P → Ω; central-twist homomorphism f → c; ρ_V → λ_V; DDP's ρ_0 → η_0; golden ratio φ → τ, with the H3 coordinate swap renamed ς and the H4 transposition δ; Euler φ(d) → \|(ℤ/d)^×\|. |
| 12 | Prop 4.3: display ℚ^T = 1 + 4 + 5 + 5 | Done, with proof via dim χ^{V4} = 1, 0, 0, 1, 2. |
| 13 | References | DKT19: J. Algebra 533 (2019) 353–375 (arXiv journal-ref). CP03: arXiv:math/0204242 added; the theorem numbering matches the arXiv text. FH03: preprint URL. Kourovka 19.28: "as cited in [SV24, §6]", since the notebook itself was not consulted. AimPL 8.6: checked against the local copy of the problem list (`aimpl/geometric-group-theory/geomartingp/08-algebraic-properties/12-…`). |
| 14 | Remark 5.4 (now 5.5): ρ injective on T for odd m | Done (Z(W) = 1 for odd m). |
| 15 | Prop 4.4: redundant non-isomorphism remark | Removed. Distinct good constituents are automatically non-isomorphic. |
| 16 | explicit_constituents.log is stale | Regenerated; it now contains the "(rank r)" fields and matches `code/README.md`. |
| 17 | lean/README.md uses the v2 numbering | Not touched, per instructions (another agent is handling `lean/`). |

---

## v3 (earlier round)

The section below is the **v3 revision after
an external AI review**, written 2026-11-07. The older sections below it (the v1 audit and the v2 response to the
cold referee) use the **old theorem numbering**; the old-to-new correspondence is in `code/README.md`.

## v3: external review → verified? → how handled

The review came from another AI system that saw only `main.tex`. Every claim in it was treated as a hypothesis. I
checked each one by exact computation (`code/indep/explicit_constituents.py`, log
`code/logs/explicit_constituents.log`) and/or by reading the cited source.

| # | Review point | Verified? | How handled |
|---|---|---|---|
| 1a | D4: U⁻ = span{u_ij} is reducible, because J(u_ij) = u_kl commutes with W(D4) | **CONFIRMED** (exact): J commutes with all generators on U⁻. Its ±1 eigenspaces are 3-dimensional and each is good (⟨χ,χ⟩ = ⟨χ,perm⟩ = 1). On the even sign group, χ_ij = χ_kl when {i,j} ⊔ {k,l} = {1,2,3,4}. | **This was an error in v2** (Remark 5.3 claimed U⁻ good for D_n, n ≥ 4). Fixed: Prop 5.2 now requires n ≥ 5, and the new Prop 5.3 handles D4 with the frame module. |
| 1b | E-type simple roots: α_k = e_{k−1} − e_{k−2} (3 ≤ k ≤ 8) in Bourbaki's coordinates | **CONFIRMED.** The v2 text had α_k = e_{k−2} − e_{k−3}, which is wrong. The code always used the correct roots (`rootsys.py`, `roots.py`: α_3 = e_2 − e_1, …, α_8 = e_7 − e_6); `explicit_constituents.py bourbaki` prints them. | **Error in the v2 text, fixed** in Appendix A. The paper now states the ambient space ℝ^8, the 1-based coordinates, and that E7 and E6 use α_1..α_7 and α_1..α_6 inside ℝ^8. |
| 2 | Use Aut(W) (Franzsen–Howlett Thm 31) instead of Out(W/Z) | **CONFIRMED by reading the source**: the authors' preprint https://www.maths.usyd.edu.au/u/bobh/fh02.pdf, Theorem 31 and the discussion before it (Prop 30, R(W) vs Inn·Gr). Statement: for B_n, D_n, E6, E7, E8, F4, H3, H4, Aut(W) = R(W)·A(W), where A(W) consists of central twists w ↦ w f(w) with f: W → Z(W). R(W) = Inn·Gr except for H3 and H4, where [R : Inn] = 2. The induced actions mod Inn are exactly as the review says. **Caveats:** the journal version (Adv. Geom. 3 (2003) 301–338) could not be downloaded (the EMIS link returned HTML), so I read the preprint. The proof of Thm 31 is labelled "(Outline)" and rests on involution class sizes from Carter. Bannai (1969) and Franzsen's thesis were **not** consulted. | **Adopted** as Lemma 4.1. Prop 4.1 and the Out(W/Z) enumeration moved to Appendix B as corroboration. For the six exceptional types the Main Theorem does **not** depend on FH alone: Appendix B controls all of Aut(W/Z) independently (by computer for E6, E7, H3, H4, F4; by hand for E8). FH is essential only for the uniform B_n/D_n proofs for all n. |
| 3 | Uniform B_n (n ≥ 3) and D_n (n ≥ 5) via the weights χ_ij; D4 via frames | **CONFIRMED.** Proof written. Exact checks: B3–B6 and D5–D7 (weights distinct and nontrivial, sign-fixed vectors fixed, U⁻ good, negating e_n has eigenvalues ±1). D4: frame module good (dimension 2), W induces S3 on frames, both witnesses exist for all six graph automorphisms. **Minor nuance:** the review says "triality permutes the frames". Our explicit isometries realising the graph automorphisms happen to act trivially on frames. This is harmless, since only the coset modulo W matters and W already induces the full S3. | Props 5.2 and 5.3. Presented as a demonstration of the method (these cases are known). |
| 4 | Explicit exceptional constituents | **CONFIRMED** (exact): see the details below the table. | Props 4.2–4.6, Lemma 4.5. The computations are kept as Appendix A cross-checks. The Baake–Moody reference suggested by the review was **not** added (not verified); the icosian model is proved directly in Lemma 4.5. |
| 5a | Outline should conclude R(φ′\|_P) = ∞ and then R(φ) = R(φ′) | Correct | Fixed (Introduction, Overview). |
| 5b | Delete "hπ need not preserve U"; in the stable case it does | **CONFIRMED**: v ∈ U ∩ hπU, and both are isotypic components, so they are equal. | Sentence deleted. πU = U is now part of hypothesis (i). The swap case states πU₁ = U₂ explicitly. |
| 5c | Mark the useful constituents; prove or drop the H4 remainder claim | — | The table lists the constituent used in bold. The H4 remainder is now **proved** (Wedderburn: 1 + 9 + 9′ + 16 + 25). |
| 6 | Related work: DDP09 Thm 4.7, DKT Thm 3.3, Hiss–Lutowski | **CONFIRMED by reading.** DDP09 (TMNA 34 (2009) 353–373), journal PDF, Thm 4.7: the flat-manifold criterion, quoted in the paper. DKT (arXiv:1709.07649v4, J. Algebra 2019), Thm 3.3: R(φ) = ∞ ⇔ det(1 − AD) = 0 for some A ∈ F (citing DP11 Cor 3.10). Hiss–Lutowski (arXiv:2412.10206): an *announcement* (proof in a separate preprint) that every finite group has the E1-property. | Added to the introduction. The novelty claim is sharpened as requested. The D5 attribution is shortened. |
| 7a | Dihedral: the criterion works iff (m odd and 3\|m) or 4\|m | **Partly confirmed.** For **odd m** I proved it (Remark 5.4): a good constituent exists iff 3\|m, and then U_3 with π ∈ S3 × {±1} gives witnesses. Computation agrees for odd m ≤ 21. The **even-m half (4\|m) is NOT verified**: ρ is not injective on T for even m, and `uniform_check.py` is unreliable there (it reports `pi realises theta: False` for some classes). | Odd case included as a remark. The even case is **not adopted**, and the paper says "we have not analysed even m". |
| 7b | R∞ for A/[P,P] | — | Not claimed. |
| 8 | Restructure and shorten; Lean paragraph; wording | — | Done. The new order is introduction / reflection lattice / criterion / exceptional / classical / appendices. Program names and runtimes moved to `code/README.md` (Appendix A only points there). The rate-limit sentence is removed, the (R)/(NA) discussion shortened, and "automorphism-free" removed. The AI reviews are described as AI reviews, not peer review. Added a Lean paragraph per `lean/README.md`. The title and abstract follow the review, adapted to what is proved. |

Details for row 4:
- **E6/E7/E8.** SRG parameters (36,15,6,6), (63,30,13,15), (120,63,30,36). Three orbitals. Spectra 3^15 (−3)^20; 3^35 (−5)^27; 3^84 (−9)^35. Dimensions match the earlier certificates (15/20, 27/35, 35/84). The perpendicular root counts and ranks are as tabulated in the proof of Prop 4.2. **Correction to the review's suggestion:** root counts alone do not identify the E6 subsystems (A3 and A2×A2 both have 12 roots), so the proof also uses the ranks.
- **H3.** 5 frames; the frame module is good and 4-dimensional; π₀ acts as a transposition on frames, with eigenspace dimensions (3, 1).
- **F4.** Frames [4,4,4] in both classes. U_long is moved only by s1, s2, and U_short only by s3, s4. π₀ swaps them; (s1π₀)² has eigenvalue −1 on U_short.
- **H4.** The icosian group closes; s_r acts on lines by x ↦ r x⁻¹ r; ⟨left, right, inversion⟩ = ρ(W) (order 7200); the matrix-coefficient space is 16-dimensional and good.
- **Correction (H4):** the natural Galois-type outer representative Ψ (Galois composed with the rotation j ↦ k, k ↦ −j) has **order 4** on lines and is not an involution. Only after composing with a suitable inner element x ↦ a x a⁻¹ does it act as conjugation by a transposition, with dimensions (10, 6). The paper says this. Ψ is in the same outer class as the original π₀.

**New open items (v3).**
* FH Thm 31 has now been checked in the published version (Adv. Geom. 3 (2003) 301–338, doi:10.1515/advg.2003.018, Thm 31 on pp. 329–330, same numbering as the preprint, typo α_χ also present). Its proof is an outline in both versions. For B_n/D_n with n > 7 the uniform proof rests on it.
* The Lean development (not modified) uses the v2 numbering and the stronger `hOut` hypothesis. It does not formalise the FH-based argument or the explicit constituents.
* Textbook section numbers (G2) are still unchecked, and so are the Cohen–Paris GAP computations (G8). Note that for B4, B6, D4 and D6, Cohen–Paris also use GAP (their Lemmas 3.5 and 4.4); this is now disclosed.

---

# (v1/v2) AUDIT: Property R∞ for A(E6), A(E7), A(E8), A(F4), A(H3), A(H4)

Audit date: 2026-11-07. Auditor: AI (Claude). No human expert has checked this yet.
Inputs audited: `s2-rinf/REPORT.md` (with its prior-art addendum), `s2-rinf/code/*`, `pa-rinf/notes.txt`, and the
downloaded papers. Output: `paper/main.tex` (references below are to its numbering).

**Verdict.** The Main Theorem is proved in the manuscript, subject to:
1. standard cited facts: Cohen–Paris; Brieskorn plus the free H₁ of hyperplane complements;
2. the exact computer certificates, each reproduced by two independent programs;
3. ~~for E8 only, one literature input from the ATLAS~~ **(revision)** E8 is now handled by a proof by hand
   (paper Prop. 4.2), using no ATLAS input and no computer.

**Disclosure (revision).** Cohen–Paris Thm 1.4 is itself computer-assisted for exactly these types: GAP
calculations in [CP03, Prop. 5.4, Cor. 5.5] (H4, F4, E6, E7, E8), and [CP03, Lemma 5.1] (H3). We have not re-run
them, so the Main Theorem depends on them. The paper now says so.

I found no mathematical error in the argument. Several steps were implicit or only numerically checked in the
original work and are now proved or certified exactly (see "fixed" below).

Status legend: **verified** = full proof written and checked, or exact certificate reproduced; **fixed** =
original statement was wrong, incomplete or only numerical, and has been corrected or completed; **cited** =
relies on the literature (statement checked against the source where possible); **gap** = not verified.

## Claim-by-claim table

("Where" refers to the first version, except where marked "rev.". In the revision: Table 1 data is Prop. 4.4; D5 is Prop. 5.2; inversion is Prop. 6.2; the E8 Out is Prop. 4.2.)

| # | Claim | Where | Status | Notes |
|---|---|---|---|---|
| 1 | P = ker(A→W) is characteristic in A (A irreducible spherical) | Thm 2.3 | **cited, statement checked** | Cohen–Paris, J. Group Theory 6 (2003), Thm 1.4, quoted verbatim from arXiv:math/0204242: "Let A be an irreducible Artin group of spherical type. Then CA is a characteristic subgroup of A." Franco–Paris (arXiv:math/0411193) extends this to reducible spherical types; it is not needed here. |
| 2 | f: A → ℤ^R ⋊ W, s ↦ (e_s, s), is well defined | Lemma 2.4 | **verified** | Self-contained proof: the reflection sequences of both alternating words are {(st)^j s : 0≤j<m}. Equivalent to Cohen–Paris Lemma 3.7(1). Machine check: `check.py` (float) and `indep_check.py` (exact) for all types. |
| 3 | f(P) = 2ℤ^R; f induces H₁(P;ℤ) ≅ 2ℤ^R; the A-action is ρ(ā), a permutation with no signs | Prop 2.6 | **verified (modulo cited rank)** | Surjectivity and equivariance proved algebraically. Injectivity uses H₁(P) ≅ ℤ^{|R|}: Brieskorn π₁(M) = P, plus H₁ of a hyperplane complement being free on meridians [Bri73, OT92 Ch. 5]. Standard; theorem numbers not given. Consistency: f(Δ²) = 2Σe_r verified by machine. |
| 4 | ker ρ = Z(W), so ρ(W) ≅ W/Z(W); φ_W induces θ on ρ(W) | Lemma 2.2 | **verified** | |
| 5 | M_φ ρ(w) M_φ⁻¹ = ρ(φ_W(w)); M_{ι_a φ} = ρ(ā) M_φ | Cor 2.9 | **verified** | |
| 6 | Schur step: N commuting with ρ(W) acts on a good constituent U by ±1 | Lemma 2.11 | **verified** | Uses multiplicity one in ℚ^R (in fact over ℂ) and the lattice U ∩ ℤ^R. |
| 7 | Certificates: (i) commutant scalar ⇒ good constituent; (ii) ⟨χ,χ⟩ = ⟨χ,perm⟩ = 1 ⇒ good constituent | Lemma 2.12 | **verified** | `certify.py` read line by line. It checks A_ω·B = μ·B exactly for every orbital matrix A_ω on the exact kernel B of X−λI, where X = Σc(A+Aᵀ) lies in the commutant. Floats are used only to pick λ. This certifies rationality (U is the kernel of a rational matrix), absolute irreducibility and multiplicity one (over ℂ). |
| 8 | Existence of π realising θ for all automorphism classes | Rem 3.2, 3.4; Prop 4.1 | **fixed (made explicit)** | The REPORT asserted this without proof. Now: inner θ → π = ρ(g); outer θ → gπ₀. `out_check.py` proves every automorphism maps ρ(R) onto ρ(R) (H3, F4, H4, D5, E6, E7), which gives π directly. The original `eig.py` builds π from θ by π(r) = θ(r) and checks πρ(s_i)π⁻¹ = θ(ρ(s_i)) on generators, which suffices. |
| 9 | Stable case (i) of the criterion | Thm 3.1 | **verified; fixed** | The REPORT's phrase "ρ(W)π has elements with eigenvalue ±1 on U" implicitly assumes πU = U. The written proof does not need this (for v∈U with hπv = cv, M_χv = c·hπv = v). For H3 and H4, π₀U = U holds anyway, checked exactly. |
| 10 | Swap case (ii) (F4) | Thm 3.1 | **verified; fixed** | The brief mentioned an "anticommuting J" argument, which does not appear in the REPORT. We wrote a direct proof: M_χ² v = c₁c₂T²v = v, and u = v + M_χ v ≠ 0 because U₁ ∩ U₂ = 0. This needs π₀(U₁) = U₂ exactly. Originally this was checked only numerically (`eig.py`); it is now certified exactly by `indep_check.py`. |
| 11 | Reidemeister facts (a)–(d), incl. R(ψ\|_H) ≤ [G:H]·R(ψ) | Lemma 2.1 | **verified** | Full proofs. (d) needs neither normality of H nor ψ(H) = H beyond ψ(H) ⊆ H. |
| 12 | Out(W/Z) = 1 for E6 | Prop 4.1 | **verified (two programs)** | `fastaut.py E6` rerun: \|Aut\| = 51840 = \|Inn\| (2.4 min now; 24 min originally). `out_check.py`: 4 involution classes (36, 45, 270, 540); one Inn-orbit of Coxeter tuples. |
| 13 | Out(W/Z) = 1 for E7 | Prop 4.1 | **fixed (upgraded)** | The REPORT took this from the ATLAS. It is now computed: `out_check.py` enumerates all 1,451,520 elements (7 s). Involution classes: 63, 315, 945, 3780; the reflection class is the unique class of size 63; one Inn-orbit. Cross-check: `out_check_stab.py`. |
| 14 | Out(W/Z) = 1 for E8 | Prop 4.2 | **verified by hand (revision)** | [G,G] = W⁺/±1 has index 2 and is characteristic. Outer involutions are w² = 1 with det −1, hence k odd; by the Steinberg argument they are products of k orthogonal reflections. So they form exactly two classes: ρ(T) (120) and triple products (37800, one class by transitivity on orthogonal triples, E8 ⊃ E7 ⊃ D6). Hence ρ(T) is preserved. Lemma 3.5 (sign choice on the tree, isometry, simple systems) then shows θ is inner. Confirmed by `referee_e8_involutions.py` and `out_check_stab.py`. The former gap G1 is closed. |
| 15 | \|Out(W/Z)\| = 2 for H3, H4, F4, with explicit outer π₀ | Prop 4.1(b) | **verified (two programs)** | Original brute force rerun (`certify_outer.py`). Independent: Galois conjugation √5 ↦ −√5 composed with a coordinate swap (H3, H4), and L(x) = (x1+x2, x1−x2, x3+x4, x3−x4) for F4. `indep_check.py` verifies that π₀ normalises ρ(W), that it is outer, and its action on constituents. |
| 16 | Good constituents: H3 {4}; H4 {16, 25}; F4 {2_short, 2_long}; E6 {15, 20}; E7 {27, 35}; E8 {35, 84}; D5 {4, 5, 10}; each moved by simple reflections | Prop 4.3, Table 1 | **verified (two methods)** | `certify.py` rerun (commutant method). `indep_check.py` uses fresh code: exact roots, class-sum eigenspaces and exact characters, for all types except E8. For E8 it uses fresh-code commutant (rank-3 action, 3 orbitals). |
| 17 | Outer witnesses | Prop 4.3 | **verified (two programs)** | `certify_outer.py` rerun: H3 (3, 1); H4 (10, 6), (15, 10); F4 swap 1, 1, 1, 1. `indep_check.py`: for H3 and H4, h = 1 works for both signs; for F4, h = 1 (ε = +1) and h = s₁ (ε = −1). |
| 18 | Classification corollary (all irreducible spherical, rank ≥ 2) | Intro | **cited, checked** | Calvez–Soroko abstract (A_n, B_n, D4, I2(m)) and SV24 Thm 1 (D_n, n ≥ 6) checked. D5 is credited to SV24 in Soroko 2610.13904 §1 ("spherical groups of type D_n, n ⩾ 5, in [SV24]"). SV24 v2 still states D5 as a conjecture, and Paris–Soroko 2606.26082 does not discuss R∞. **Gap G5**: the journal version of SV24 was not seen. |
| 19 | D5 independent proof | Prop 5.1 | **verified** | Out = 1 (both programs). The diagram involution is inner via diag(−1,−1,−1,−1,1) ∈ W(D5). Good constituents 4, 5, 10. |
| 20 | Centre-fixing automorphisms are elementary | Rem 6.1 (rev.) | **verified** (elementary proof) | Elementary argument via H₁(A): the image of Δ has coordinate sum \|T\| ≠ 0. The FLT/Jabara sentence was deleted in the revision. |
| 21 | Inversion has R = ∞ in every non-free-abelian Artin group | Prop 5.3 | **verified** (uniform proof) | Invariant max\|v_r − v_{srs}\| for W-part s. Not new (Soroko 2610.13904 Thm 1 for non-spherical; Juhász). `check.py` random tests: 0 violations. |
| 22 | Novelty of the Main Theorem | Intro | **gap (G6)** | Prior-art sweep confidence 80–85%; citation-graph APIs failed. |

## Errors and inaccuracies found in the original REPORT / brief

1. **D5 attribution** (REPORT table): "Paris–Soroko arXiv:2606.26082 and Soroko arXiv:2610.13904". Paris–Soroko does
   not prove R∞; it computes Aut(A(D5)). R∞ for D5 is credited to SV24 in Soroko 2610.13904. *(Already corrected in
   the REPORT addendum; the manuscript follows the correction.)*
2. **"Theorem 3 ... and D5"** presented D5 as new. It is not; the manuscript presents it as an independent proof.
3. **Kourovka 19.28.** The brief calls Conjecture (NA) "Kourovka 19.28". Per SV24 §6, Kourovka 19.28 is
   Conjecture (R) (f.g. residually finite ⇒ R∞ or solvable-by-finite); (NA) is a weaker variant. Corrected in the
   manuscript.
4. **E7 relied on the ATLAS.** This is now unnecessary (computed). Only E8 still uses the ATLAS.
5. **Implicit assumption πU = U in the stable case.** It is not needed (proof rewritten); it holds anyway for
   H3 and H4.
6. **Swap case relied on a numerical check of π(U₁) = U₂.** It is now certified exactly.
7. **Existence of π** for every automorphism was asserted without argument. It is now proved
   (Remarks 3.2 and 3.4, plus the reflection-preservation check).
8. **Runtime.** The REPORT says E6 takes about 25 min; the rerun took 2.4 min (load-dependent).
9. **Minor (code).** `certify_outer.py D5` crashes because D5 has no outer class; this is benign and documented.
   `grp.py` and `pgrp.py` are identical copies (only `pgrp.py` is shipped).
10. **Minor (JMS Cor. H).** The prior-art notes say it "needs a separating vertex"; the manuscript adds that the
    defining graph of a spherical type is complete, so it has none.

No error was found in: Theorem 1 logic, the Schur/lattice step, the finite-index inequality, the twisting step,
the certificates, or any computed number (all reproduced).

## Remaining gaps (the PDF no longer contains [GAP] markers; open items are listed here only)

* ~~G1~~ **closed** (E8 by hand).
* **G2.** The paper now cites Humphreys and Orlik–Terao without section numbers. The standard facts used are: order
  of st is m; W transitive on simple systems and on roots of a simply-laced system; centre of W; H₁ of an
  arrangement complement. Precise locations still need to be filled in by a human. They are not marked in the PDF.
* ~~G3~~ **closed**: the FLT/Jabara sentence was deleted from Remark 6.1.
* **G8 (revision).** The Main Theorem depends on the GAP computations in Cohen–Paris §5, which we have not
  re-verified (disclosed in the paper).
* **G4.** Charney–Crisp Prop. 9 (Aut(A(F4))) is seen only as quoted by Jones–Mangioni–Sartori (context only).
* **G5.** D5 credit: the SV24 journal version was not seen.
* **G6.** Novelty: the literature search was incomplete.
* **G7.** AI-only review; an expert check is needed.


## Revision after the cold referee report (minor revision; no mathematical errors found)

| # | Referee point | Action taken | Where |
|---|---|---|---|
| 1 | Make E8 free of the ATLAS and of the computer | Done. New Prop. 4.2: Step 1, [G,G] index 2 and characteristic; Step 2, outer involutions = ρ(T) (120) ⊔ one class of 37800, via the Steinberg-theorem proof of Carter's Lemma 5 and transitivity on orthogonal triples; Step 3, new Lemma 3.5 (sign choice on the tree; isometry; W simply transitive on simple systems). The S3/ATLAS argument was **dropped**, not kept as a remark, so C_G(S) = 1 and Steinberg's Out(Ω8+(2)) are no longer needed; the ATLAS is mentioned only as agreeing. Referee scripts added as `code/indep/referee_*.py` with README entries and logs. Gap G1 removed. | §3 Lemma 3.5, §4 Prop. 4.2 and remark |
| 2 | Disclose that Cohen–Paris Thm 1.4 is computer-assisted | Done, with exact locations: Prop. 5.4 and Cor. 5.5 (GAP) for H4, F4, E6, E7, E8. Also disclosed: Lemma 5.1 (GAP) for H3. | §2.2 after Thm 2.3 |
| 3 | Qualify "two independent programs" for Out(E7), Out(E8) | Done. E7: one enumeration (`out_check.py`), plus `uniform_check.py` (same author, separate code), plus the stabiliser check and Lemma 3.5 by hand for the second step; `fastaut.py` was not run for E7. E8: now by hand. | Prop. 4.1 proof |
| 4a | Prop 4.3 F4 wording | Fixed: only s1, s2 act nontrivially on U_long, only s3, s4 on U_short. | Prop. 4.4 |
| 4b | Table 1, F4 "2·9" justification invalid | Fixed: rank-3 action on each 12-point class, 10 orbitals = 3+3+2+2, shared constituents = trivial and 9-dim. Same care taken for H3 (degrees of A5) and H4 (now "ψ+ψ′, dim 18"; dimension 9 only numerical). | text after Table 1 |
| 4c | Remark 5.2 FLT/Jabara sentence | Deleted. | Remark 6.1 |
| 5 | Calvez–Soroko for I2(m) | Fixed: I2(m) uses virtual freeness of A/Z and Fel'shtyn's theorem (checked in arXiv:2106.13260 §3). | Intro §1.1 |
| 6 | Add Dhanwani–Kumar–Naik–Singh arXiv:2409.10270 | Added (crystallographic quotients of virtual Artin groups; R∞ for right-angled virtual Artin groups). | Intro, bibliography |
| 7 | Weaken Thm 3.1 hypothesis to α induced from Aut(A) | Done ("for every φ ∈ Aut(A)"). Added Cor. 2.9: θ_φ preserves the permutation character χ_T. This is what rules out the S6 outer automorphism. | Thm 3.1, Cor. 2.9 |
| 8 | Notation clashes | Fixed: reflections are now 𝒯 (vs R(φ)); complement is X (vs M_φ); twisted automorphism is φ′ (vs χ_U, χ_T); Q = hπ; Σ = Galois map; κ for inversion on ℤ^T⋊W. ρ is still used for both the action and its permutation matrix, as stated explicitly. | throughout |
| 9 | Housekeeping | GGO17 → J. Algebra 474 (2017) 393–423 (confirmed from the DKNS reference list). Marin → Geom. Dedicata 182 (2016) 233–247 (from a citing paper via web search). Prop 2.6 stated for all spherical A. README now says `eig.py D5` (and `certify_outer.py D5`) crash, as expected. | bibliography, Prop 2.6, README |
| 10 | Remove all [GAP] markers | Done. Unresolved items (textbook section numbers, G2) moved here. "[Author names]" and the AI placeholder kept; the placeholder now also mentions the AI cold referee. | PDF, AUDIT |
| 11 (optional) | Uniform treatment of all spherical types | **Partly done.** A_n: full proof by hand for all n ≥ 2 (Prop. 5.1; S6 outer excluded by χ_T). B_n (3–7), D_n (4–7, incl. D4 triality and D5), I2(9), I2(15), and E6, E7, F4, H3, H4: verified by exact computation (`uniform_check.py`, Prop. 5.2). General B_n, D_n: good constituent U⁻ and the reflection-preserving step proved by hand (Remark 5.3). **Missing:** that every Aut(A)-induced automorphism of W/Z preserves reflections, for all n. I2(m), m odd: a good constituent exists iff 3 \| m. For m prime ≥ 5 the criterion cannot apply (End = real cyclotomic field with infinitely many units). Even m not analysed (ρ not injective on T); computation finds no good constituent for m = 6, 10, 18. Stated honestly in Remark 5.4. | §5 |

New claim rows (revision):

| # | Claim | Status |
|---|---|---|
| 23 | Lemma 3.5 (reflection-preserving ⇒ inner·diagram, simply-laced; B_n variant) | **verified** (hand proof) |
| 24 | Prop 4.2 (Out(W(E8)/±1) = 1) | **verified** (hand proof; computational confirmation) |
| 25 | Prop 5.1 (A_n, Aut-free) | **verified** (hand proof; uses Young's rule and Aut(S_k)) |
| 26 | Prop 5.2 (finite verification for B_n ≤ 7, D_n ≤ 7, I2(9), I2(15)) | **verified** by `uniform_check.py` (one program, author-written) |
| 27 | Remark 5.4 (I2(m), m odd: good constituent iff 3 \| m) | **verified** (hand argument; matches computation) |


## Update: Franzsen–Howlett journal version

The user supplied the published PDF. Theorem 31 is on pp. 329–330, with the same number and statement as the preprint. The proof is labelled "(Outline)". Item (9) also has the α_χ typo. The paper's citation is updated to the DOI and page numbers, and the preprint caveat is removed.
