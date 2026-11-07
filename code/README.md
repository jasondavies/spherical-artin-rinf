# Computational verification

Install the pinned dependencies in the repository's `requirements.txt`, then run from the repository root:

```sh
python3 scripts/verify.py --only python
```

The runner disables Python optimisation, sets numerical libraries to one thread, checks dependency versions, requires a successful exit and the `ALL CHECKS PASSED` marker, and writes separate logs plus `verification/python-summary.json`. Use `python3 scripts/verify.py --clean` to include the clean PDF and Lean builds.

## Proof inputs and exact cross-checks

All paths below are relative to `code/`. The runner executes each row and first runs the fault-injection tests in `test_certificate_guards.py`. Those tests require empty or partial constituent/witness data and empty command lines to fail.

| Script | Mathematical purpose |
|---|---|
| `indep/explicit_constituents.py` | Exact constructions of E-type graph eigenspaces, H3/F4 frames, H4 matrix coefficients and icosians, D4 frames and signed-pair witnesses. Checks rational ranks, multiplicities and sign/swap witnesses. |
| `indep/exceptional_srg.py` | Independent integer-coordinate checks of E6/E7/E8 graph parameters and perpendicular subsystem counts and ranks. |
| `indep/out_check.py H3 F4 H4 E6 E7` | Full holonomy automorphisms: involution classes followed by inner orbits of Coxeter tuples. Required for the exceptional quotient cases treated computationally; E8 is proved by hand. |
| `indep/out_check_stab.py E7 E8` | Schreier–Sims check of the reflection-preserving stage. E8's full automorphism result is proved in the paper. |
| `indep/dihedral_quotient.py` | Actual I₂(5) extension, lattice, inverse, all ten determinants, torsion, and two exact twisted-class counts. |
| `indep/quotient_families.py --max-m 46` | Finite corroboration of the uniform family proofs: direct root-line counts through rank 12, character equations through rank 120, conjugacy orbits in B6 and D5–D12, and all dihedral m = 3,…,46. |
| `indep/indep_check.py H3 F4 H4 D5 E6 E7` | Independent exact character and multiplicity certificates, braid relations and outer witnesses. |
| `indep/indep_check.py commutant:E8 commutant:H3 commutant:F4` | Exact orbital/commutant certificates. |
| `certify.py H3 F4 H4 E6 E7 E8 D5` | Exact rational checks of candidate constituent bases and scalar commutants. |
| `certify_outer.py H3 F4 H4` | Exact scalar commutants, stable/swap images and sign witnesses, with required constituent multiplicities and both signs checked. |

The unbounded classical and dihedral statements are proved algebraically in the manuscript. Checking finitely many ranks or parameters does not prove them.

## Expected mathematical outputs

- E6, E7, E8 have graph parameters (36,15,6,6), (63,30,13,15), (120,63,30,36), and nontrivial constituent dimensions (15,20), (27,35), (35,84).
- H3's frame constituent has dimension 4 with outer eigenvalue multiplicities (3,1). F4 has exchanged dimension-two constituents and witnesses for both signs of the squared operator. H4's matrix-coefficient constituent has dimension 16 with outer multiplicities (10,6).
- Full holonomy outer automorphism orders are 2,2,2,1,1 for H3,F4,H4,E6,E7. The optional D5 check gives order 1. E8's reflection-preserving automorphisms are inner.
- I₂(5): adjusted determinants are 2 at the identity, 22 at the four nonidentity rotations, and −10 at the five reflections. Centraliser counts are 1+6+6+5=18. The full enumeration gives 13 orbits of size ten and five of size two. The determinant average is 14 and is not R.

## Arithmetic and additional tools

The `indep/` exact checks use root systems over ℚ(√5) in `rootsys.py`, permutation routines in `permgroup.py`, and rational row reduction. The dihedral and family checkers are self-contained SymPy programs. The SRG checker constructs its integer coordinates independently.

`certify.py` and `certify_outer.py` use numerical calculations to locate candidate data, then check dimensions, scalar actions, stable/swap images and eigenvector identities exactly. Required constituent counts and both signs are checked explicitly; empty candidate lists cannot certify a positive case. The main proof inputs are also reconstructed from exact root systems by `indep/`.

Additional corroboration tools are retained for mathematical use:

- `indep/out_check.py D5`: optional full-holonomy computation. The main proof handles D5 uniformly with the classical family; the seven-case Lean account still includes D5.
- `indep/small_holonomy.py`, `indep/f4_blocks.py`, `indep/e8_involutions.py`: independent small-group or involution calculations.
- `indep/uniform_check.py`: finite exploration of the character-preserving criterion. Failure of that criterion is not itself a proof of failure of R∞.
- `indep/numerical_frames.py` and `indep/numerical_icosians.py`, using `quadratic_field.py`: numerical corroboration, including QR decompositions, pseudoinverses or rounded characters. They are not proof certificates.
- `roots.py`, `analyze.py`, `pgrp.py`, `fastaut.py`, `eig.py`, `check.py`: root, group and exploratory utilities. Their numerical output is not a substitute for an exact certificate.

Run scripts in `code/indep/` from that directory when invoking these additional tools directly. The verification runner handles working directories automatically.
