/-
# The Coxeter matrix of type D₅

Mathlib's `CoxeterMatrix.D n` (Mathlib v4.35.0) does **not** give the `D₅` diagram: for `n = 5` it
has `m₃₄ = 3` in addition to `m₂₄ = m₂₃ = 3`, i.e. a triangle `2–3–4` (an infinite Coxeter group).
We therefore define the `D₅` matrix explicitly, in the Bourbaki-style indexing used by
`code/indep/rootsys.py` (chain `0–1–2–3`, node `4` attached to `2`).
-/
import Mathlib

namespace ArtinRinf

set_option backward.isDefEq.respectTransparency false in
/-- The Coxeter matrix of type `D₅`:
```
    o --- o --- o --- o
                |
                o
```
-/
def D₅ : CoxeterMatrix (Fin 5) where
  M := !![1, 3, 2, 2, 2;
          3, 1, 3, 2, 2;
          2, 3, 1, 3, 3;
          2, 2, 3, 1, 2;
          2, 2, 3, 2, 1]

/-- Documentation of the discrepancy: Mathlib's `CoxeterMatrix.D 5` has `m₃₄ = 3`, ours has
`m₃₄ = 2`. -/
theorem mathlib_D5_differs : (CoxeterMatrix.D 5).M 3 4 = 3 ∧ D₅.M 3 4 = 2 := by decide

end ArtinRinf
