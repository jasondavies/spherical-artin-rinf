# Computational verification

Install the pinned dependencies in the repository's `requirements.txt`, then run from the repository root:

```sh
python3 scripts/verify.py --only python
```

The runner disables Python optimisation, sets numerical libraries to one thread, checks dependency versions, requires a successful exit and the `ALL CHECKS PASSED` marker, and writes separate logs plus `verification/python-summary.json`. Use `python3 scripts/verify.py --clean` to include the clean PDF and Lean builds.

## Proof inputs and exact cross-checks

All paths below are relative to `code/`. The runner executes each row and first runs the fault-injection tests in `test_certificate_guards.py`. Those tests require empty or partial constituent/witness data, corrupt eigenbases, failed SRG identities, a nontrivial holonomy centre and empty command lines to fail. They also check wrapped Lean axiom reports and reject unexpected axioms or a missing presented-quotient theorem.

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

## Why the holonomy search is exhaustive

Appendix B uses `indep/out_check.py` for H3, F4, H4, E6 and E7. Its inputs are the exact root-line permutations constructed by `indep/rootsys.py`. The following steps describe the completeness argument and its implementation.

1. `permgroup.enumerate_group` starts at the identity and repeatedly multiplies by every simple generator until no new permutation remains. Equality is equality of the entire permutation array. The size limit raises an exception; it never returns a truncated group.
2. Every enumerated element is tested for being a nonidentity involution. Union–find under conjugation by the simple generators partitions all these involutions into conjugacy classes. The checker requires that only reflection classes have the reflection-class sizes. Since automorphisms preserve order and conjugacy-class size, every automorphism preserves the reflection set. It also checks injectivity of the reflection images and triviality of the centre.
3. `search(tup, H)` maintains the pointwise stabiliser `H` of the chosen reflection tuple. It lists every possible next reflection whose pair-product orders agree with those of the corresponding simple generators. These conditions are invariant under `H`, so the search takes one representative of each `H`-orbit and recurses with its stabiliser. This induction covers exactly one representative of every inner orbit of admissible tuples; it is not a random or bounded-depth sample. Reflection-image injectivity identifies point stabilisers with centralisers of the corresponding reflections.
4. Each length-rank tuple must generate the whole holonomy group, checked by exact permutation-group order. Such a tuple satisfies the Coxeter relations and gives a surjection W → W/Z(W). Its kernel has order |Z(W)|, which is one or two in these types. A normal subgroup of order two is central, so the kernel is precisely Z(W). Thus every retained tuple induces an automorphism, and every automorphism supplies a retained tuple up to inner conjugation.
5. The resulting orbit counts must be 2, 2, 2, 1, 1 for H3, F4, H4, E6, E7. A mismatch causes a nonzero exit. `out_check_stab.py` independently checks the reflection-preserving stage for E7 and E8; it does not establish reflection preservation by itself. The E8 full-holonomy result uses the paper's hand proof.

For the other exceptional proof inputs, Proposition 4.1 (E types) is checked by `exceptional_srg.py` and `explicit_constituents.py`; Propositions 4.2, 4.3 and 4.5 (H3, F4, H4) and Lemma 4.4 (icosians) use `explicit_constituents.py`. The independent character and outer-witness programs provide additional checks. The seven conditional Lean theorems follow the separate Franzsen–Howlett route described in `lean/README.md`; their success does not by itself certify Appendix B's full-holonomy computations.

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
