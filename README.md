# Twisted conjugacy in spherical Artin groups and their crystallographic quotients

The paper proves three results for irreducible spherical types of Coxeter rank at least two:

- **Theorem A:** every corresponding Artin group has property R∞.
- **Theorem B:** the quotient Γ = A/[P,P] has R∞ whenever A has Coxeter rank at least three. In rank two, of type I₂(m), it has R∞ exactly when 4 divides m, or m is odd and 3 divides m.
- **Proposition C:** Γ of type I₂(5) admits an explicit automorphism with Reidemeister number 18.

The main proof proceeds through the quotients. Absolutely irreducible rational constituents of multiplicity one, with explicit sign or swap witnesses, force eigenvalue one after a holonomy twist. Character arguments handle the classical families uniformly. In the negative dihedral families, explicit integral maps preserve the actual crystallographic extension and have finite Reidemeister number.

Theorem B implies the rank-at-least-three part of Theorem A because [P,P] is characteristic. The dihedral Artin-group case is known. The direct Artin-group proof using Franzsen–Howlett is documented beside the [Lean sources](lean/DIRECT_PROOF.md) and has a conditional formalisation. Appendix C states its scope and dependencies.

## Read the paper

- [Manuscript](paper/spherical-artin-rinf.pdf) and [LaTeX source](paper/spherical-artin-rinf.tex).
- [Proof and source audit](AUDIT.md): dependencies, sensitive proof steps, literature attribution and remaining submission work.
- [Reviewer note](REVIEWER_NOTE.md): a focused review brief.
- [Computational guide](code/README.md) and [Lean guide](lean/README.md).

## Reproduce

The public repository is <https://github.com/jasondavies/spherical-artin-rinf>. The paper pins its Python and Lean sources and dependency files to commit [`3edce8ab5c74ab58d9990249524e2bbc5ea28754`](https://github.com/jasondavies/spherical-artin-rinf/tree/3edce8ab5c74ab58d9990249524e2bbc5ea28754). This revision includes the unconditional formalisation of Proposition C. There is currently no release tag or archive DOI.

Use Python 3.12, a TeX installation with `pdflatex` and the packages imported by `paper/spherical-artin-rinf.tex`, and Elan/Lake. Python dependencies, including SymPy's mpmath dependency, and the Lean/Mathlib toolchain are pinned.

```sh
git clone https://github.com/jasondavies/spherical-artin-rinf.git
cd spherical-artin-rinf
git checkout --detach 3edce8ab5c74ab58d9990249524e2bbc5ea28754
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
(cd lean && lake exe cache get)
.venv/bin/python scripts/verify.py --clean
```

The command runs all required Python certificates and selected exact cross-checks, builds the PDF from clean auxiliary files, cleans and rebuilds this Lean package while retaining the Mathlib cache, and checks the axiom report. Each run writes its logs and summary to a separate `verification/runs/<run-id>/` directory. The summaries in `verification/` point to the latest runs. It exits nonzero on a failed check, an unresolved LaTeX reference or an overfull box.

For individual components, use `--only python`, `--only paper` or `--only lean`. The Lean build defaults to four threads; `--threads N` changes this. The largest Lean certificate modules can require about 25 GB each, so allow substantial memory or reduce concurrency. Python checks take roughly a minute on the tested machine; the clean Lean build takes considerably longer.

After a successful full verification run, `python3 scripts/package_review.py` creates `verification/review-package.zip` and `verification/review-package.zip.sha256`. Verification hashes all repository inputs (including documentation, scripts and dependency pins), checks that they are unchanged at the end of the run, and records the generated PDF and log hashes. Packaging rejects changed, added or removed inputs, a changed PDF or log, and any later verification run. Run the full workflow again after edits or a component run. A clean Git status alone does not establish verification.

The computational commit pin identifies the code revision; checking it out also selects the manuscript stored at that revision. The complete submitted snapshot is the review ZIP, identified by its companion SHA-256 checksum. It contains the exact verified manuscript, PDF, sources, dependencies and logs. `REVIEW_PACKAGE.json` records the verification run, a digest of the complete source-and-PDF snapshot, each file's checksum, the base commit and whether there were uncommitted changes. The archive excludes dependency caches and Git history. Retain the ZIP and checksum together when submitting it; a public release tag or archive DOI can additionally identify that complete snapshot.

## Verification scope

The exact Python calculations are proof inputs for the exceptional constituents and holonomy automorphisms. The unbounded classical and dihedral classification is proved in the text; finite checks corroborate it. The I₂(5) count is checked both by centraliser orbits and by enumeration of all 140 translation-twisted classes.

Lean verifies the direct Artin-group argument for D5, E6, E7, E8, F4, H3 and H4, conditional on explicitly stated cited results. It also proves Proposition C for the presented quotient A(I₂(5))/[P,P]: the affine map has kernel exactly [P,P], and the transferred automorphism has Reidemeister number 18. This result has no external mathematical hypotheses. The full quotient classification remains outside Lean. See the Lean guide for the precise hypotheses.

Jason Davies is the author. The mathematical arguments, programs, Lean development and manuscript were developed by AI systems under his direction; the paper includes an AI transparency statement and a fuller disclosure. No independent human expert review has been recorded.

## Citation

Jason Davies. *Twisted conjugacy in spherical Artin groups and their crystallographic quotients*. Preprint, 2026.

Machine-readable citation metadata is provided in [CITATION.cff](CITATION.cff). When citing the computational material, also identify the commit used. A preprint identifier or archive DOI will be added when available.

## License

Copyright 2026 Jason Davies.

The original contents of this repository, including the manuscript, documentation, Python code and Lean development, are licensed under the Apache License 2.0; see [LICENSE](LICENSE). Third-party dependencies retain their own licences.
