/-
# Balanced binary lookup trees

Large data tables (type E8) are stored as balanced binary trees, so that the kernel looks up an
entry with `O(log n)` comparisons instead of walking a `![...]` vector linearly.
-/
import Mathlib

namespace ArtinRinf

/-- A balanced binary lookup tree: `node m l r` sends indices `< m` to `l`, the rest to `r`. -/
inductive BT (α : Type) where
  | leaf : α → BT α
  | node : ℕ → BT α → BT α → BT α

/-- Lookup. -/
def BT.get {α : Type} : BT α → ℕ → α
  | .leaf a, _ => a
  | .node m l r, i => if i < m then l.get i else r.get i

end ArtinRinf
