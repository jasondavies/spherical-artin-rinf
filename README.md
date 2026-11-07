# Twisted conjugacy in spherical Artin groups and their crystallographic quotients

The paper proves three results for irreducible spherical types of Coxeter rank at least two:

- **Theorem A:** every corresponding Artin group has property R∞.
- **Theorem B:** the quotient Γ = A/[P,P] has R∞ whenever A has Coxeter rank at least three. In rank two, of type I₂(m), it has R∞ exactly when 4 divides m, or m is odd and 3 divides m.
- **Proposition C:** Γ of type I₂(5) admits an explicit automorphism with Reidemeister number 18.

The main proof proceeds through the quotients. Absolutely irreducible rational constituents of multiplicity one, with explicit sign or swap witnesses, force eigenvalue one after a holonomy twist. Character arguments handle the classical families uniformly. In the negative dihedral families, explicit integral maps preserve the actual crystallographic extension and have finite Reidemeister number.

Theorem B implies the rank-at-least-three part of Theorem A because [P,P] is characteristic. The dihedral Artin-group case is known. The direct Artin-group proof using Franzsen–Howlett is documented beside the [Lean sources](lean/DIRECT_PROOF.md) and has a conditional formalisation. Appendix C states its scope and dependencies.

## Read the paper

- [Manuscript](paper/main.pdf) and [LaTeX source](paper/main.tex).
- [Proof and source audit](AUDIT.md): dependencies, sensitive proof steps, literature attribution and remaining submission work.
- [Reviewer note](REVIEWER_NOTE.md): a focused review brief.
- [Computational guide](code/README.md) and [Lean guide](lean/README.md).

## Reproduce

Use Python 3.12, a TeX installation with `pdflatex` and the packages imported by `paper/main.tex`, and Elan/Lake. Python dependencies, including SymPy's mpmath dependency, and the Lean/Mathlib toolchain are pinned.

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
(cd lean && lake exe cache get)
.venv/bin/python scripts/verify.py --clean
```

The command runs all required Python certificates and selected exact cross-checks, builds the PDF from clean auxiliary files, cleans and rebuilds this Lean package while retaining the Mathlib cache, and checks the axiom report. Logs and machine-readable summaries are written to `verification/`. It exits nonzero on a failed check, an unresolved LaTeX reference or an overfull box.

For individual components, use `--only python`, `--only paper` or `--only lean`. The Lean build defaults to four threads; `--threads N` changes this. The largest Lean certificate modules can require about 25 GB each, so allow substantial memory or reduce concurrency. Python checks take roughly a minute on the tested machine; the clean Lean build takes considerably longer.

After a successful full verification run, `python3 scripts/package_review.py` creates `verification/review-package.zip`. It contains the current manuscript source and PDF, Python and Lean sources, pinned dependency files, documentation, and the logs from that run. `REVIEW_PACKAGE.json` records a SHA-256 checksum for every included file and identifies whether the snapshot contains uncommitted changes. The archive excludes dependency caches and Git history.

## Verification scope

The exact Python calculations are proof inputs for the exceptional constituents and holonomy automorphisms. The unbounded classical and dihedral classification is proved in the text; finite checks corroborate it. The I₂(5) count is checked both by centraliser orbits and by enumeration of all 140 translation-twisted classes.

Lean verifies the direct Artin-group argument for D5, E6, E7, E8, F4, H3 and H4, conditional on explicitly stated cited results. It does **not** formalise the full quotient classification or the Reidemeister number 18. See the Lean guide for the precise hypotheses.

The argument, code and text were developed with substantial AI assistance. No human expert review has been recorded. Author information and the contribution statement must be completed before submission.
