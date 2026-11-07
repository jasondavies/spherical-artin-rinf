# Lean 4 / Mathlib formalisation of the R∞ criterion for exceptional spherical Artin groups

This directory formalises the argument of `../paper/main.tex` (version v3.1) in Lean 4 with Mathlib.
Theorem numbers below refer to v3. The old v2 → v3 table is in `../code/README.md`. The
formalisation covers:

* the Reidemeister-number lemmas (Lemma 2.1);
* the abstract criterion: Theorem 3.3, Lemma 3.1, Corollary 2.5 and Remark 3.5, including the
  F4 swap variant;
* the Artin group as a presented group, the homomorphism `f : A → ℤ^T ⋊ Perm T` (Lemma 2.3), and
  `P^ab` as a permutation module (Proposition 2.4, apart from the cited rank statement);
* the finite certificates for **all seven types D5, E6, E7, E8, F4, H3 and H4**, checked by the
  Lean kernel with `decide +kernel`. These are commutant-scalar constituents (Lemma 3.2(i)) and the ±1
  witnesses;
* **Lemma 4.1 (via Franzsen–Howlett), for all seven types.** Given the cited theorem
  `FranzsenHowlett M` (`Aut(W) = R(W)·A(W)`), every automorphism of `A` induces on `ρ(W) = W/Z` a
  conjugation by an element of `ρ(W)` or of `ρ(W)π₀`. The Coxeter-group bridge is proved in Lean.
  The finite part is a kernel-checked search-tree certificate. This yields theorems
  `artin_X_R_infty_FH` with **no `hOut`**;
* for **H3 and F4**, also the full computation of `Out(W/Z(W))` (Appendix B), by enumeration.

The cited deep inputs are **explicit hypotheses** of the final theorems. They are not global
`axiom`s, so each theorem's type shows what it depends on.

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`. These are the same pins as in the user's
other projects.

## Build

```
cd lean
lake exe cache get          # Mathlib oleans (fast if ~/.cache/mathlib is populated)
LEAN_NUM_THREADS=4 lake build
```

Measured build time (v3.1, with D5; **as of commit 296176a**), from a clean `.lake/build` with the Mathlib oleans already
present: **12 min 38 s wall clock, 46 min CPU**. This was with `LEAN_NUM_THREADS=4`, on a shared
16-core machine, 2026-11-07. The D5 modules (`Types/D5`, `Types/D5FH`) take about 10 s each. The
slowest modules:

| module | time | what |
|---|---|---|
| `Types/F4Out` | 7.7 min | `Out` enumeration for F4 |
| `Types/E7FH` | 3.9 min | search tree, E7 |
| `Types/E8FH` | 3.1 min | search tree, E8 |
| `Types/H4FH` | 2.6 min | search tree, H4 |
| `Data/E8`, `Data/F4Out` | about 3 min each | mostly writing `.ilean` files for large tree literals |
| `Types/E7` | 3.2 min | certificates |
| `Types/H4` | 2.5 min | certificates |
| `Types/E8/Orb*` | 2.7 min each | run in parallel |

Peak memory: the certificate modules `Types/E7` and `Types/H4` reached about **25 GB** RSS each (measured in the
v2 build), so the build needs a machine with ample RAM. The newer `*FH` (search-tree) modules need less: about
**11 GB** each when run separately.

After `lake build`, `lake env lean scripts/print_axioms.lean` prints the axioms and statements. The output quoted
below is as of commit 296176a.

There is **no `sorry`**, **no `native_decide`** and **no `axiom`** anywhere in `ArtinRinf/`.
All finite computations use `decide +kernel`, so they are evaluated by the Lean kernel. The trusted
base is therefore the kernel only, not the compiler. The `#print axioms` output is below.
`decide +kernel` adds no axiom.

## Main theorems

Common notation:

* `M = CoxeterMatrix.X` is **Mathlib's** Coxeter matrix, except for D5 (see below).
* `ArtinGroup M` is the presented group `⟨S | Π(s,t;m) = Π(t,s;m)⟩`.
* `M.Group` is Mathlib's Coxeter group `W`.
* `pure M = ker (ArtinGroup M → M.Group)`.
* `N` is the number of reflections: 15, 24, 60, 36, 63, 120, and 20 for D5.
* `reidemeisterAut φ : ℕ∞` is the number of `φ`-twisted conjugacy classes, with `⊤` meaning
  infinitely many.

All main theorems conclude `∀ φ : ArtinGroup M ≃* ArtinGroup M, reidemeisterAut φ = ⊤`.

**Recommended form (v3): `ArtinRinf.X.artin_X_R_infty_FH`, in `Types/XFH.lean`, for all seven types.**

```lean
theorem ArtinRinf.E8.artin_E8_R_infty_FH
    (hW  : Finite M.Group)                                                   -- W finite
    (hCP : (pure M).Characteristic)                                          -- Cohen–Paris
    (hBr : Nonempty (Abelianization (pure M) ≃* Multiplicative (Fin 120 → ℤ)))  -- Brieskorn
    (hFH : FranzsenHowlett M) :                                              -- Franzsen–Howlett
    ∀ φ : ArtinGroup M ≃* ArtinGroup M, reidemeisterAut φ = ⊤
```

`FranzsenHowlett M` (file `FH.lean`) reads: every `α : M.Group ≃* M.Group` equals `β ∘ γ`, where:

* `β` is reflection-preserving: it maps `{w s_i w⁻¹}` into itself;
* `γ` is a central twist: `w⁻¹ γ(w) ∈ Z(W)` for all `w`.

This is [FH03, Thm. 31], the input to the paper's Lemma 4.1. It is a statement about Mathlib's
Coxeter group alone and does not mention the exported data.

**Type D5** (paper v3.1, Prop. 5.2 with `n = 5`, Remark 5.3).

* **Coxeter matrix.** Mathlib v4.35.0's `CoxeterMatrix.D 5` is **not** the `D₅` matrix: it has
  `m₃₄ = 3` besides `m₂₃ = m₂₄ = 3`, a triangle, so its Coxeter group is infinite. This is
  documented by the lemma `mathlib_D5_differs`. `CoxD5.lean` therefore defines `ArtinRinf.D₅`
  explicitly: the chain `0–1–2–3` with node 4 attached to 2, as in `rootsys.py`.
* **Constituent.** The good constituent is the unique 10-dimensional one. This is the paper's
  `U⁻ = span{e_[ei+ej] − e_[ei−ej]}`.
* **Outer case.** `Z(W) = 1` and every automorphism is inner, so `π₀ = 1`.

**Per-theorem hypotheses**

| type | theorem | hypotheses | outer case |
|---|---|---|---|
| H3 | `H3.artin_H3_R_infty_FH` | `hW`, `hCP`, `hBr`, `hFH` | stable, `π₀ = θ_Σ` |
| H3 | `H3.artin_H3_R_infty'` | `hW`, `hCP`, `hBr` only | `Out` enumerated in Lean |
| F4 | `F4.artin_F4_R_infty_FH` | `hW`, `hCP`, `hBr`, `hFH` | swap, `π₀ = θ_L` |
| F4 | `F4.artin_F4_R_infty'` | `hW`, `hCP`, `hBr` only | `Out` enumerated in Lean |
| H4 | `H4.artin_H4_R_infty_FH` | `hW`, `hCP`, `hBr`, `hFH` | stable; `π₀` is the Galois-type permutation from `code/indep`, a non-inner reflection-preserving element, hence in the same `Inn`-coset as the paper's `θ_Ψ` |
| E6 | `E6.artin_E6_R_infty_FH` | `hW`, `hCP`, `hBr`, `hFH` | all inner |
| E7 | `E7.artin_E7_R_infty_FH` | `hW`, `hCP`, `hBr`, `hFH` | all inner |
| E8 | `E8.artin_E8_R_infty_FH` | `hW`, `hCP`, `hBr`, `hFH` | all inner |
| **D5** | `D5.artin_D5_R_infty_FH` | `hW`, `hCP`, `hBr` (`P^ab ≅ ℤ^20`), `hFH` | all inner (Franzsen–Howlett Thm 31(3): `Aut(W) = R(W) ≅ W`) |
| all seven | `X.artin_X_R_infty` (v2 form, kept for compatibility; for D5 `hOut` says every automorphism of `W` is inner) | `hW`, `hCP`, `hBr`, `hOut` | — |

`hOut : OutGeneratedBy D.ρ.range π₀` says that every automorphism of the permutation group
`ρ(W) ≤ Perm T` is conjugation by an element of `ρ(W)` or of `ρ(W)π₀`. It is the v2-style
hypothesis. It is no longer needed for any type.

The `_FH` theorems and the H3/F4 primed theorems are logically independent routes. The primed
theorems avoid Franzsen–Howlett altogether by enumerating `Aut(ρ(W))`.

## What is formally proved (no hypotheses beyond those in the statements)

| Paper (v3) | Lean | File |
|---|---|---|
| Lemma 2.1(a): `R(φ) ≥ R(φ̄)`, for quotients, the abelianisation, and any surjective intertwining map | `reidemeister_le_of_surjective`, `reidemeister_quotient_le`, `reidemeister_abelianization_le` | `Reidemeister.lean` |
| Lemma 2.1(c): `R(ι_g ∘ φ) = R(φ)` | `reidemeister_inner_comp` | `Reidemeister.lean` |
| Lemma 2.1(d): `R(φ\|_H) ≤ [G:H]·R(φ)`, hence `R(φ\|_H)=∞ ⇒ R(φ)=∞` | `reidemeister_restrict_le`, `reidemeister_eq_top_of_restrict` | `Reidemeister.lean` |
| Lemma 2.1(b), the part used: if `B ∈ M_T(ℤ)` has eigenvalue 1 over `ℚ` (equivalently `det(B−1)=0`), then `R = ∞` | `reidemeister_matEnd_eq_top`, `reidemeister_matEnd_eq_top_of_det` | `FreeAbelian.lean` |
| §2: `θ_φ` on `ρ(W)` is well defined because `ker ρ` is `φ`-invariant | `inducedAut`, `rho_map_eq_one` | `Criterion.lean` |
| Corollary 2.5: `M_φ ρ(a) = ρ(φa) M_φ`, `M_{ι_a φ} = ρ(a) M_φ`, functoriality | `Mmat_pmat`, `Mmat_conj`, `Mmat_trans` | `Criterion.lean` |
| Lemma 3.1 (lattice step): a rational eigenvalue of `N ∈ GL_T(ℤ)` on a nonzero rational vector is `±1` | `eigenvalue_eq_one_or_neg_one` | `Criterion.lean` |
| Theorem 3.3, stable case (i) and swap case (ii) | `reidemeister_eq_top_of_witness` | `Criterion.lean` |
| Remark 3.4 (reduction to cosets of `Inn`), packaged | `Witness.mul_left`, `rinf_of_outGeneratedBy` | `Criterion.lean` |
| Artin group, `A → W`, braid relations from Coxeter relations | `ArtinGroup`, `ArtinGroup.lift`, `toCoxeter`, `braid_of_coxeter` | `ArtinGroup.lean` |
| Lemma 2.3: `f : A → ℤ^T ⋊ Perm T`, `σ_i ↦ (e_{s_i}, ρ(s_i))` | `ReflData.f` (braid relations checked per type) | `Pure.lean`, `Aff.lean` |
| Prop. 2.4: `f(P) ⊆ 2ℤ^T`; equivariant surjection `P^ab → ℤ^T`; isomorphism given `hBr` (Hopfian argument) | `f_pure`, `ebar_equivariant`, `ebar_surjective`, `permModuleIso` | `Pure.lean` |
| Lemma 3.2(i): orbital certificate ⇒ every matrix commuting with `ρ(W)` is scalar on `U` | `OrbitalCert`, `commScalar_of_cert` | `Certificate.lean` |
| §4.2 (Props. 4.2–4.6), Prop. 5.2 (`D₅`, `U⁻`), Appendix A: good constituents and ±1 witnesses, all seven types | `commScalar_U0` (and `U1` for F4), `witness_inner`, `witness_outer` | `Types/X.lean` |
| **Lemma 4.1, Coxeter part:** `φ ∈ Aut(A)` induces `φ_W ∈ Aut(W)` (needs `hCP`). With `hFH`, `ρ(φ(σ_i))` is a reflection permutation, using `Z(ρ(W)) = 1`. | `ArtinGroup.coxAut`, `RpData.image_refl`, `RpData.center_trivial` | `FH.lean` |
| **Lemma 4.1, finite part:** every tuple of reflections with the Coxeter orders of the simple reflections is conjugate to the simple tuple by `ρ(W)` or `ρ(W)π₀` (search-tree soundness) | `TreeCert.conj` | `FH.lean` |
| **Lemma 4.1, the per-type trees** | `TC`, `tree_ext_ok`, `tree_leaf_ok` | `Types/XFH.lean` |
| Theorem 3.3 + Lemma 4.1 combined | `ReflData.rinf_FH` | `FH.lean` |
| Appendix B for H3 and F4: `Out(ρ(W))` generated by `π₀` | `H3.hOut`, `F4.hOut` (via `OutCert.outGeneratedBy`) | `OutCert.lean`, `Types/H3Out.lean`, `Types/F4Out.lean` |

### The search-tree certificate (Lemma 4.1, finite part)

* **Reduction to reflection tuples.** A reflection-preserving `θ` is determined by the reflections
  `x_i = θ(s_i)`. Their pairwise products have the exact Coxeter orders `m_ij`.
* **Orbit/stabiliser reduction.** The certificate fixes `x_0` up to `ρ(W)`-conjugacy, then `x_1`
  up to the pointwise stabiliser of the chosen prefix, and so on.
  * Each node of the tree is a prefix of orbit representatives.
  * For every admissible next entry `c`, the certificate gives a word `h` in the generators. The
    word fixes the prefix and sends the representative of a child node to `c`.
  * Every leaf is the image of the simple tuple under an explicit word, times `π₀` if needed.
* **Kernel check and size.** The kernel checks admissibility (exact orders, as `isOrdB`), the
  words and the leaves. The trees are tiny:

  | type | nodes | admissible extensions | leaves |
  |---|---|---|---|
  | H3 | 5 | 21 | 2 |
  | F4 | 9 | 50 | 2 |
  | E6 | 7 | 68 | 1 |
  | H4 | 6 | 88 | 2 |
  | E7 | 8 | 123 | 1 |
  | E8 | 9 | 241 | 1 |
  | D5 | 7 | 40 | 1 |

  Words have length ≤ 119. They are found by lifting to `W` and running the descent algorithm in
  `scripts/export_tree.py`.

This is the computational analogue of `code/indep/out_check_stab.py`. It never enumerates
`ρ(W)`, so it works for E8 (`|ρ(W)| = 348364800`).

## Hypotheses standing for cited results

| Hypothesis | Meaning | Source | Status |
|---|---|---|---|
| `hW : Finite M.Group` | the Coxeter group is finite | classical (Coxeter) | Hypothesis. Used only for `[A:P] < ∞`. |
| `hCP : (pure M).Characteristic` | `P = ker(A→W)` is characteristic | Cohen–Paris 2003, Thm 1.4 (paper Thm 2.2). Computer-assisted (GAP). | Hypothesis. |
| `hBr : Nonempty (P^ab ≃* ℤ^N)` | `H₁(P;ℤ)` is free abelian of rank `N = \|T\|` | Brieskorn + Orlik–Terao (used in Prop. 2.4) | Hypothesis. The equivariant identification is then **proved**. |
| `hFH : FranzsenHowlett M` | `Aut(W) = R(W)·A(W)` | Franzsen–Howlett 2003, Thm 31 (paper §4.1) | Hypothesis of the `_FH` theorems. |
| `hOut` (v2 form only) | `Aut(ρ(W)) = Inn·⟨π₀⟩` | computation (Appendix B) | Not needed any more. **Proved** for H3 and F4. |

## Trust in the finite data

The exported data live in `ArtinRinf/Data/*.lean` and are produced by the following scripts:

| script | exports |
|---|---|
| `scripts/export_data.py` | generator permutations, orbital labels with a BFS spanning forest, integer constituent bases, `π₀`, witness words and vectors |
| `scripts/export_tree.py` (new) | reflection-permutation tables and the search trees |
| `scripts/export_out.py` | H3 and F4 enumerations of `ρ(W)` |

* **Sources.** The scripts read `../code/indep/rootsys.py` and `indep_check.explicit_pi0`. They
  write nothing in `code/`, and they set `dont_write_bytecode`.
* **Untrusted.** Every property used is re-checked by `decide +kernel`, so wrong data would make
  the build fail.
* **Large tables.** For E8 and F4-Out, tables are balanced binary trees (`BT.lean`), so kernel
  lookups are logarithmic.
* **Generated Lean files.** `scripts/gen_types.py` and `scripts/split_e8.py` generate
  `Types/{H4,E6,E7,E8,D5}.lean` and `Types/E8/*.lean`. `scripts/gen_fh.py` generates
  `Types/XFH.lean`.
* **Hand-written Lean files.** `Types/H3.lean`, `Types/F4.lean`, `Types/H3Out.lean` and
  `Types/F4Out.lean`.

Checked per type by `decide +kernel`:

* generators are involutions that fix their own reflection;
* the braid relations hold in `ℤ^T ⋊ Perm T`;
* the Coxeter relations hold in `(ℤ/2)^T ⋊ Perm T`;
* every reflection is conjugate to a simple one;
* the orbital certificate, and that every orbital matrix acts on `U` as a scalar;
* the ±1 witnesses;
* `π₀` is an involution normalising `ρ(W)`;
* reflection permutations: `rp(s_i) = ρ(s_i)`, generator-equivariance, `π₀`-equivariance and
  injectivity of `rp` (which gives `Z(ρ(W)) = 1`);
* exact orders `m_ij` of `ρ(s_i s_j)`;
* the search tree.

## Remaining gaps

* `hW`, `hCP`, `hBr` and `hFH` are not formalised. They are classical or cited theorems.
  Cohen–Paris is itself computer-assisted.
* The hand proofs of v3 are not formalised:
  * the explicit constituents of §4.2 (strongly regular graphs for the E types, frames for H3 and
    F4, the icosian model for H4);
  * Lemma B.1 / Prop. B.2.

  The formalisation instead uses computer-found constituents, re-checked by the kernel through the
  commutant certificate. This covers the same mathematical statement: for the E types, the three
  orbitals are certified, so the commutant is span{I, J, A_⊥}. The strongly-regular-graph identity behind Prop. 4.2 is
  not formalised separately.
* Lemma 3.2(ii) (character certificate), §5 (A_n, B_n, D_n, including the new uniform B_n/D_n
  argument) and the dihedral discussion are not formalised.
* The identification of `T = Fin N` with the set of reflections of `W` is not formalised.
  * The `_FH` theorems do link the data to `W`: `ρ = ρ_W ∘ μ`, where `ρ_W` is the lift of the
    generator permutations to `M.Group`, and `rp(s_i) = ρ(s_i)` with equivariance.
  * Only `hBr` refers to `N`.

## `#print axioms`

```
$ lake env lean scripts/print_axioms.lean
'ArtinRinf.reidemeister_quotient_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.reidemeister_inner_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.reidemeister_restrict_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.reidemeister_matEnd_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.eigenvalue_eq_one_or_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.reidemeister_eq_top_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.rinf_of_outGeneratedBy' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.ReflData.rinf' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.H3.artin_H3_R_infty' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.H3.artin_H3_R_infty'' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.F4.artin_F4_R_infty' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.F4.artin_F4_R_infty'' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.H4.artin_H4_R_infty' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.E6.artin_E6_R_infty' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.E7.artin_E7_R_infty' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.E8.artin_E8_R_infty' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.H3.artin_H3_R_infty_FH' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.F4.artin_F4_R_infty_FH' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.H4.artin_H4_R_infty_FH' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.E6.artin_E6_R_infty_FH' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.E7.artin_E7_R_infty_FH' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.E8.artin_E8_R_infty_FH' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.D5.artin_D5_R_infty' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.D5.artin_D5_R_infty_FH' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.ReflData.rinf_FH' depends on axioms: [propext, Classical.choice, Quot.sound]
'ArtinRinf.ReflData.TreeCert.conj' depends on axioms: [propext, Classical.choice, Quot.sound]
ArtinRinf.H3.artin_H3_R_infty' : Finite ArtinRinf.H3.M.Group →
  (ArtinRinf.ArtinGroup.pure ArtinRinf.H3.M).Characteristic →
    Nonempty (Abelianization ↥(ArtinRinf.ArtinGroup.pure ArtinRinf.H3.M) ≃* Multiplicative (Fin 15 → ℤ)) →
      ∀ (φ : ArtinRinf.ArtinGroup ArtinRinf.H3.M ≃* ArtinRinf.ArtinGroup ArtinRinf.H3.M),
        ArtinRinf.reidemeisterAut φ = ⊤
ArtinRinf.F4.artin_F4_R_infty' : Finite ArtinRinf.F4.M.Group →
  (ArtinRinf.ArtinGroup.pure ArtinRinf.F4.M).Characteristic →
    Nonempty (Abelianization ↥(ArtinRinf.ArtinGroup.pure ArtinRinf.F4.M) ≃* Multiplicative (Fin 24 → ℤ)) →
      ∀ (φ : ArtinRinf.ArtinGroup ArtinRinf.F4.M ≃* ArtinRinf.ArtinGroup ArtinRinf.F4.M),
        ArtinRinf.reidemeisterAut φ = ⊤
ArtinRinf.E8.artin_E8_R_infty : Finite ArtinRinf.E8.M.Group →
  (ArtinRinf.ArtinGroup.pure ArtinRinf.E8.M).Characteristic →
    Nonempty (Abelianization ↥(ArtinRinf.ArtinGroup.pure ArtinRinf.E8.M) ≃* Multiplicative (Fin 120 → ℤ)) →
      ArtinRinf.OutGeneratedBy ArtinRinf.E8.D.ρ.range 1 →
        ∀ (φ : ArtinRinf.ArtinGroup ArtinRinf.E8.M ≃* ArtinRinf.ArtinGroup ArtinRinf.E8.M),
          ArtinRinf.reidemeisterAut φ = ⊤
ArtinRinf.E8.artin_E8_R_infty_FH : Finite ArtinRinf.E8.M.Group →
  (ArtinRinf.ArtinGroup.pure ArtinRinf.E8.M).Characteristic →
    Nonempty (Abelianization ↥(ArtinRinf.ArtinGroup.pure ArtinRinf.E8.M) ≃* Multiplicative (Fin 120 → ℤ)) →
      ArtinRinf.FranzsenHowlett ArtinRinf.E8.M →
        ∀ (φ : ArtinRinf.ArtinGroup ArtinRinf.E8.M ≃* ArtinRinf.ArtinGroup ArtinRinf.E8.M),
          ArtinRinf.reidemeisterAut φ = ⊤
def ArtinRinf.FranzsenHowlett.{u_1} : {B : Type u_1} → CoxeterMatrix B → Prop :=
fun {B} M =>
  ∀ (α : M.Group ≃* M.Group),
    ∃ β γ, ArtinRinf.IsReflPres β ∧ ArtinRinf.IsCentralTwist γ ∧ ∀ (w : M.Group), α w = β (γ w)
ArtinRinf.D5.artin_D5_R_infty_FH : Finite ArtinRinf.D5.M.Group →
  (ArtinRinf.ArtinGroup.pure ArtinRinf.D5.M).Characteristic →
    Nonempty (Abelianization ↥(ArtinRinf.ArtinGroup.pure ArtinRinf.D5.M) ≃* Multiplicative (Fin 20 → ℤ)) →
      ArtinRinf.FranzsenHowlett ArtinRinf.D5.M →
        ∀ (φ : ArtinRinf.ArtinGroup ArtinRinf.D5.M ≃* ArtinRinf.ArtinGroup ArtinRinf.D5.M),
          ArtinRinf.reidemeisterAut φ = ⊤
def ArtinRinf.D₅ : CoxeterMatrix (Fin 5) :=
{ M := !![1, 3, 2, 2, 2; 3, 1, 3, 2, 2; 2, 3, 1, 3, 3; 2, 2, 3, 1, 2; 2, 2, 3, 2, 1], isSymm := ArtinRinf.D₅._proof_1,
  diagonal := ArtinRinf.D₅._proof_2, off_diagonal := ArtinRinf.D₅._proof_3 }
```

## Files

```
lakefile.toml, lean-toolchain, lake-manifest.json
ArtinRinf.lean                 root module (imports everything below)
ArtinRinf/Reidemeister.lean    twisted classes, R(φ) ∈ ℕ∞, Lemma 2.1 (a), (c), (d)
ArtinRinf/FreeAbelian.lean     Lemma 2.1 (b) (eigenvalue 1 on ℤ^T ⇒ R = ∞)
ArtinRinf/PermMatrix.lean      permutation action and permutation matrices
ArtinRinf/Criterion.lean       M_φ, Cor. 2.5, Lemma 3.1, Theorem 3.3, Remark 3.5, θ_φ
ArtinRinf/ArtinGroup.lean      Artin groups as presented groups, A → W, P = ker
ArtinRinf/Aff.lean             R^T ⋊ Perm T with decidable equality
ArtinRinf/Pure.lean            ReflData, f (Lemma 2.3), P^ab ≅ ℤ^T (Prop. 2.4), generic main theorem
ArtinRinf/Certificate.lean     orbital certificates (Lemma 3.2(i)), witnesses from integer data
ArtinRinf/OutCert.lean         Out(ρ(W)) from an enumeration certificate (Appendix B, H3/F4)
ArtinRinf/FH.lean              Franzsen–Howlett hypothesis, φ_W, Lemma 4.1 bridge, search-tree
                               certificates, rinf_FH
ArtinRinf/BT.lean              balanced binary lookup trees for large tables
ArtinRinf/Data/{H3,F4,H4,E6,E7,E8}.lean      exported data (generated)
ArtinRinf/Data/{H3,F4}Out.lean               enumerations of ρ(W) (generated)
ArtinRinf/Data/{H3,F4,H4,E6,E7,E8}Tree.lean  reflection permutations + search trees (generated)
ArtinRinf/Types/{H3,F4}.lean                 certificates and hOut-theorems (hand-written)
ArtinRinf/Types/{H3,F4}Out.lean              Out(ρ(W)) verified; theorems with hW, hCP, hBr only
ArtinRinf/Types/{H4,E6,E7,E8}.lean           certificates and hOut-theorems (generated)
ArtinRinf/Types/E8/*.lean                    E8 certificate checks, split for parallelism (generated)
ArtinRinf/Types/{H3,F4,H4,E6,E7,E8}FH.lean   Franzsen–Howlett theorems artin_X_R_infty_FH (generated)
ArtinRinf/CoxD5.lean                         the D₅ Coxeter matrix (Mathlib's `CoxeterMatrix.D 5` is wrong)
ArtinRinf/Data/D5.lean, Data/D5Tree.lean     D5 data (generated)
ArtinRinf/Types/D5.lean, Types/D5FH.lean     D5 certificates and theorems (generated)
scripts/export_data.py, export_out.py, export_tree.py,
        gen_types.py, split_e8.py, gen_fh.py      data / file generation (untrusted)
scripts/print_axioms.lean                    #print axioms and statements of the main theorems
```
