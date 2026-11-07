# Code for "Property R∞ for the Artin groups of types E6, E7, E8, F4, H3, H4"

Requirements: Python 3 (tested with 3.12), numpy (2.5.1), sympy (1.14.0). No GAP or Sage needed.

All runs below were single-threaded (`OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1`) on a shared, heavily loaded
16-core machine on 2026-11-07. Logs are in `logs/`. The logs of the original exploratory runs are kept,
unchanged, in `original_logs/`.

## Layout

| file | origin | purpose |
|---|---|---|
| `roots.py` | original | floating-point root systems (rounded keys), permutations of reflections `C.rp` |
| `analyze.py` | original | orbital matrices (basis of the commutant of the permutation module) |
| `certify.py` | original | **exact** certificate of good constituents (commutant criterion, Lemma 2.12(i)) |
| `pgrp.py` | original | permutation group enumeration, brute-force Aut count (`aut_count`) |
| `fastaut.py` | original | vectorised brute-force count of Aut(ρ(W)) (used for E6) |
| `eig.py` | original | numerical constituents; outer automorphism and the permutation π (Remark 3.4) |
| `certify_outer.py` | original | **exact** certificate of outer-case witnesses (H3, F4, H4) |
| `check.py` | original | numerical sanity checks: braid relations for f, f(Δ²)=2Σe_r, inversion invariant |
| `indep/rootsys.py` | new, independent | **exact** root systems over Q(√5) |
| `indep/permgroup.py` | new | group enumeration (numpy uint8 rows) |
| `indep/indep_check.py` | new, independent | character-theoretic certificate (Lemma 2.12(ii)), explicit outer π₀, exact witnesses; `commutant:<type>` mode for E8 |
| `indep/out_check.py` | new, independent | Out(ρ(W)) via involution classes plus Inn-orbits of Coxeter tuples (H3, F4, H4, D5, E6, E7) |
| `indep/out_check_stab.py` | new | Schreier–Sims version of step (2) only (E7, E8) |
| `indep/uniform_check.py` | new (revision) | criterion with weakened hypothesis (θ induced by Aut(A) ⇒ preserves χ_T) for A_n, B_n, D_n, I2(m) and exceptional types |
| `indep/referee_own_check.py` | **written by the cold referee**, independent | Aut(G) count without assuming reflection preservation; commutant and character certificates; witnesses (H3, F4) |
| `indep/referee_e8_involutions.py` | **referee** | all involution classes of W(E8)/±1; confirms Prop. 4.2, step 2 |
| `indep/referee_f4_blocks.py` | **referee** | orbital counts per reflection class for F4 (Table 1 remainder) |

The `indep/` programs do not import any of the original modules.

## Commands, runtimes, expected output

```
cd code
python3 certify.py H3 F4 H4 E6 E7 E8 D5        # 2 s     -> logs/certify.log
python3 certify_outer.py H3 F4 H4              # 9 s     -> logs/certify_outer.log
python3 check.py                               # 12 s    -> logs/check.log
python3 fastaut.py E6                          # 2.4 min (24 min under heavier load) -> logs/fastaut_E6.log
python3 eig.py D5                              # 1 s, then crashes (expected, see notes) -> logs/eig_D5.log
cd indep
python3 indep_check.py H3 F4 H4 E6 E7          # 9 s, 1.3 GB RAM (E7 enumerates 1,451,520 elements) -> logs/indep_check.log
python3 indep_check.py D5                      # <1 s    -> logs/indep_check_D5.log
python3 indep_check.py commutant:E8 commutant:H3 commutant:F4   # 2 s -> logs/indep_commutant.log
python3 out_check.py H3 F4 H4 D5 E6 E7         # 8 s, 1.3 GB RAM -> logs/out_check.log
python3 out_check_stab.py E7 E8                # 2 s     -> logs/out_check_stab.log
python3 uniform_check.py "I2(5)" "I2(6)" "I2(7)" "I2(8)" "I2(9)" "I2(10)" "I2(12)" "I2(15)" "I2(18)" A2 A3 A4 A5 A6 A7 B3 B4 B5 D4 D5 H3 F4   # ~20 s -> logs/uniform_small.log
python3 uniform_check.py B6 D6 E6 H4           # 2 s     -> logs/uniform_mid.log
python3 uniform_check.py D7 B7                 # 4 s     -> logs/uniform_big.log
python3 uniform_check.py E7                    # 7 s, 1.8 GB -> logs/uniform_E7.log
python3 referee_own_check.py H3 F4             # 2 s     -> logs/referee_own_check.log
python3 referee_e8_involutions.py              # 1.3 s   -> logs/referee_e8_involutions.log
python3 referee_f4_blocks.py                   # <1 s    -> logs/referee_f4_blocks.log
```

Expected key lines:

* `certify.log`: for each type, `exact constituent dim d ... commutant scalar: True` with
  H3: 4 (λ=32); F4: 2 (λ=20) and 2 (λ=90); H4: 16, 25; E6: 15, 20; E7: 27, 35; E8: 35, 84; D5: 4, 5, 10.
  In every case the simple generators acting nontrivially are listed; for F4 these are [0,1] on one
  constituent and [2,3] on the other.
* `certify_outer.log`: `|Out| = 2` for H3, F4, H4; `permutation pi of R realizing outer theta found, check: True`.
  `EXACT ... common kernel dim` is positive for ε = ±1 in every case (H3: 3, 1; H4: 10, 6 and 15, 10; F4: 1, 1, 1, 1).
* `check.log`: `braid rels ok True Delta^2->2*sum e_r True ... violations 0` for all six types.
* `fastaut_E6.log`: `|Aut|= 51840 |Inn|= 51840 |Out|= 1`.
* `indep_check.log`: `|rho(W)| = ...  -> True`, `centre of rho(W) has order 1`, `braid relations ... True`.
  The `GOOD` eigenspaces have `<chi,chi> = 1, <chi,perm> = 1`, with the same dimensions as certify.py
  (all types except E8). For the explicit π₀ (H3, H4, F4) the output shows `normalises rho(W): True`,
  `induced automorphism is outer: True`, and the exact image of each constituent (H3, H4: itself; F4: swapped).
  Witnesses: `True` for ε = ±1. For H3 and H4 the witness is h = element #0 (the identity). For F4 it is #0 for
  ε=+1 and #1 (= s₁) for ε=−1.
* `indep_commutant.log`: E8 has 3 orbitals; the eigenspaces of dims 84 and 35 have all orbital matrices scalar.
* `out_check.log`: `automorphisms preserve rho(R): True` and `|Out(rho(W))|` = 2, 2, 2, 1, 1, 1 for
  H3, F4, H4, D5, E6, E7. The involution class sizes for E7 are [63, 315, 945, 3780].
* `uniform_*.log`: for every A_n, B_n, D_n, E6, E7, F4, H3, H4 listed, `-> every Aut(A)-induced automorphism preserves rho(R)`,
  and for every class `criterion: ('(i)', d)` or `('(ii)', d)`. For I2(m): `FAILS` for m = 5, 6, 7, 10, 18. It holds for m = 9, 15.
  For m = 8, 12 it reports success, but ρ is not injective on T for even m, so these are not claimed in the paper.
* `referee_e8_involutions.log`: classes of involutions with w²=1 have sizes 120 (k=1), 1575, 3780, 37800 (k=3), 56700;
  there is one w²=−1 class of size 7560. The only class of size 120 is the reflections.
* `out_check_stab.log`: `|rho(W)| = 348364800` for E8; `every automorphism of rho(W) preserving rho(R) is inner: True`
  for E7 and E8.

## Notes and caveats

* `eig.py D5` and `certify_outer.py D5` both **crash** after printing the constituents and `|Out| = 1`
  (`TypeError: 'NoneType' object is not iterable`, see `logs/eig_D5.log`, `logs/certify_outer_D5.time`).
  This is expected: Out(ρ(W(D5))) = 1, so there is no outer automorphism for `outer_check` to process.
  The D5 data needed are in `certify.log`, `indep_check_D5.log` and `uniform_small.log`.
* `roots.py` and `check.py` use floating point with rounding to identify roots. All exact claims are re-derived
  from exact root systems by `indep/`.
* `certify.py` uses floating point only to choose which eigenvalues λ to test. The kernel and the scalar checks
  are exact (SymPy `DomainMatrix` over QQ).
* `certify_outer.py` checks the image π(U₁) = U₂ (F4) only numerically, in `eig.py`. The exact check is in
  `indep/indep_check.py` (`pi_0 maps constituent 0 (dim 2) exactly onto constituent 1`).
* Out(W(E8)/Z) = 1 is now proved by hand in the paper (Prop. 4.2), with no ATLAS input. `referee_e8_involutions.py`
  and `out_check_stab.py` are computational confirmations only.
