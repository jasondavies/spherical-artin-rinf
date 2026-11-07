# Artin groups 8.6: R∞ for the exceptional spherical Artin groups (new)

Source: `/home/ttuser/aimpl/geometric-group-theory/geomartingp/08-algebraic-properties/12-which-artin-groups-have-property-r.md`

**Theorem 3 (agent).** The Artin groups of types E6, E7, E8, F4, H3, H4 and D5 have property R∞.

Combined with the literature, this gives: **every irreducible spherical Artin group of rank ≥ 2 has R∞.**

| Types | Source |
|---|---|
| A_n, B_n, D4, I₂(m) | Calvez–Soroko, arXiv:2106.13260 |
| D_n, n ≥ 6 | Soroko–Vaskou, arXiv:2409.18123 |
| D5 | Paris–Soroko arXiv:2606.26082 and Soroko arXiv:2610.13904; independently reproved here |
| E6, E7, E8, F4, H3, H4 | **new**; Aut(A) is unknown for these types |

## Method (Theorem 1)

The proof does not need Aut(A). It works for any automorphism φ, as follows.

1. **The pure subgroup is preserved.** P = ker(A → W) is characteristic (Cohen–Paris), so φ(P) = P.
2. **Abelianization of P.** H₁(P; ℤ) ≅ ℤ[R], with W permuting the meridians and no signs (Brieskorn). So φ acts on H₁(P) by π·N, where:
   - π realises the induced automorphism of W/Z;
   - N commutes with W.
3. **N is ±1 on a good constituent.** Let U be a rational, absolutely irreducible constituent of ℚ[R] of multiplicity one. By Schur's lemma N acts on U as a rational scalar c, and N preserves a lattice, so c = ±1.
4. **Twist to get eigenvalue 1.** Compose φ with a suitable inner automorphism. If ρ(W)π has elements with eigenvalue +1 on U and elements with eigenvalue −1 on U, the composite has eigenvalue 1 on H₁(P). A swap version, case (ii), covers F4.
5. **Pass back up to A.** By the previous step, R(χ|_P) = ∞. Then R(χ) = ∞ by the finite-index inequality R(χ|_H) ≤ [G:H]·R(χ), and R(φ) = R(χ).

**Inputs.**
- Out(W/Z): E6, H3, H4, F4 and D5 by brute force; E7 and E8 from the ATLAS.
- Exact rational certificates for the constituents and for the ±1 witnesses in the outer-automorphism cases.

**Bonus (Proposition 4).** Inversion has R = ∞ in every Artin group that is not free abelian. The proof is explicit: the classes of t^{2k}s are pairwise distinct, detected by a twisted invariant from the map A → ℤ^R ⋊ W.

## Main session checks

- I read the proof of Theorem 1 and found it sound. The key steps all check out:
  - Schur's lemma together with lattice preservation forces c = ±1;
  - composing with inner automorphisms handles the non-trivial outer classes;
  - the finite-index Reidemeister inequality is correct.
- I re-ran `certify_outer.py H3 F4`. All ±1 and swap witnesses are confirmed exactly.
- I inspected `cert_big.log` (E7, E8, H4 constituents certified, with scalar commutant) and `e6_fast.log` (|Out| = 1).
- This is not yet an expert audit. Facts F1–F3 are cited and were not re-derived.

## Open

- Reducible spherical types. A₁×A₁ = ℤ² fails, so the precise criterion is still needed.
- Central quotients and pure subgroups of the E, F and H types.
- Removing the ATLAS dependence for E7 and E8.

## Reproduce

In `/tmp/claude-1000/-home-ttuser-aimpl/5c8074b4-afcc-48d7-ab53-b80fd70d4e74/scratchpad/s2-rinf/code/`:

- `python3 certify.py <types>` and `python3 certify_outer.py H3 F4 H4` (exact certificates)
- `python3 fastaut.py ...` (E6 takes about 25 minutes)

---
## PRIOR-ART SWEEP (main session, 2026-11-07). Details in `pa-rinf/notes.txt`

**Verdict.** The main theorem (E6, E7, E8, F4, H3, H4) appears new, with confidence about 80–85%. Coverage was limited because the citation-graph APIs failed.

- **No general theorem implies it.**
  - Fel'shtyn–Troitsky's claim (arXiv:1204.3175) would imply it, but its proof is known to be wrong (per SV24 §6). The statement is now Conjecture (NA), Kourovka 19.28.
  - The acylindrical/quasimorphism criteria (FFW23, FFIMSW, SV26) need Aut(A), which is unknown for these types.
- **D5 is NOT new.** Soroko arXiv:2610.13904 credits it to Soroko–Vaskou. Present our proof as independent.
- **The bonus result (inversion) is mostly covered** by Soroko 2610.13904, Thm 1, for non-spherical types.
- **Method precedent:** Dekimpe–Gonçalves–Ocampo (arXiv:2006.08286), which forces eigenvalue 1 via reflection-group representations. Cite it, together with Marin and Gonçalves–Guaschi–Ocampo (crystallographic quotients).
- **Possible shortcut:** in residually finite groups, R(φ) < ∞ implies φ has finitely many fixed points (Fel'shtyn–Luchnikov–Troitsky 2015). So automorphisms fixing the centre are immediate, and only the centre-inverting case needs the main argument.
- **Scoop risk: moderate–low.** Soroko is the active author, but none of his "in preparation" items cover these types. Jones–Mangioni–Sartori footnote 3 suggests a uniform route via A/Z.
- **Corrections:**
  - Cite Franco–Paris alongside Cohen–Paris for P being characteristic.
  - Paris–Soroko 2606.26082 computes Aut(D5) only; it does not prove R∞.
