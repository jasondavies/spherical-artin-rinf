/- Exact I₂(5) extension offsets in the manuscript's cyclic coordinates. -/
import ArtinRinf.Aff

namespace ArtinRinf.Dihedral5

abbrev I := Fin 5
abbrev V := I → ℤ
abbrev Hol := DihedralGroup 5

open DihedralGroup

def permFun : Hol → I → I
  | r k, i => ⟨((i.val : ZMod 5) + k).val, ZMod.val_lt _⟩
  | sr k, i => ⟨(-(i.val : ZMod 5) - k).val, ZMod.val_lt _⟩

theorem perm_left : ∀ g i, permFun g⁻¹ (permFun g i) = i := by decide +kernel
theorem perm_right : ∀ g i, permFun g (permFun g⁻¹ i) = i := by decide +kernel

def perm (g : Hol) : Equiv.Perm I := ⟨permFun g, permFun g⁻¹, perm_left g, perm_right g⟩

theorem perm_one : perm 1 = 1 := by decide +kernel
theorem perm_mul : ∀ g h, perm (g * h) = perm g * perm h := by decide +kernel
theorem perm_inv : ∀ g, perm g⁻¹ = (perm g)⁻¹ := by decide +kernel

def rotOffset : Fin 5 → V := ![![0, 0, 0, 0, 0],
    ![1, 0, 1, 1, 1],
    ![0, 1, 1, 0, 0],
    ![1, 0, 0, 0, 1],
    ![0, 1, 1, 1, 1]]

def refOffset : Fin 5 → V := ![![1, 0, 0, 0, 0],
    ![0, 1, 1, 1, 0],
    ![1, 0, 0, 1, 1],
    ![0, 1, 0, 0, 0],
    ![1, 1, 1, 1, 1]]

def offset : Hol → V
  | r k => rotOffset ⟨k.val, ZMod.val_lt k⟩
  | sr k => refOffset ⟨k.val, ZMod.val_lt k⟩

theorem offset_one : offset 1 = 0 := by decide +kernel

theorem offset_mul : ∀ g h i,
    (offset (g * h) i : ZMod 2) = (offset g i : ZMod 2) +
      (offset h ((perm g).symm i) : ZMod 2) := by decide +kernel

theorem offset_inv : ∀ g i, (offset g⁻¹ i : ZMod 2) =
    -(offset g (perm g i) : ZMod 2) := by decide +kernel

end ArtinRinf.Dihedral5
