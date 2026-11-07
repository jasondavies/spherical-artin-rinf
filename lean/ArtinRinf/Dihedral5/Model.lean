/-
# The nonsplit affine extension for I₂(5)

The holonomy is the dihedral group of order ten. Its ten translation cosets
are specified by the offsets checked in Data. The translation kernel is 2ℤ⁵.
-/
import ArtinRinf.Dihedral5.Data

namespace ArtinRinf.Dihedral5

@[ext] structure Ambient where
  v : V
  g : Hol
  deriving DecidableEq

namespace Ambient

instance : Mul Ambient := ⟨fun x y => ⟨x.v + pact (perm x.g) y.v, x.g * y.g⟩⟩
instance : One Ambient := ⟨⟨0, 1⟩⟩
instance : Inv Ambient := ⟨fun x => ⟨-pact (perm x.g⁻¹) x.v, x.g⁻¹⟩⟩

@[simp] lemma mul_v (x y : Ambient) : (x * y).v = x.v + pact (perm x.g) y.v := rfl
@[simp] lemma mul_g (x y : Ambient) : (x * y).g = x.g * y.g := rfl
@[simp] lemma one_v : (1 : Ambient).v = 0 := rfl
@[simp] lemma one_g : (1 : Ambient).g = 1 := rfl
@[simp] lemma inv_v (x : Ambient) : x⁻¹.v = -pact (perm x.g⁻¹) x.v := rfl
@[simp] lemma inv_g (x : Ambient) : x⁻¹.g = x.g⁻¹ := rfl

instance : Group Ambient where
  mul_assoc x y z := by
    ext
    · simp only [mul_v, mul_g, perm_mul, pact_mul, Aff.pact_add, Pi.add_apply]
      abel
    · exact mul_assoc _ _ _
  one_mul x := by ext <;> simp [perm_one]
  mul_one x := by ext <;> simp [Aff.pact_zero]
  inv_mul_cancel x := by
    ext
    · simp [perm_inv]
    · simp
  npow := npowRec
  zpow := zpowRec

end Ambient

/-- The extension cosets, including their parity shifts. -/
def extension : Subgroup Ambient where
  carrier := {x | ∀ i, (x.v i : ZMod 2) = (offset x.g i : ZMod 2)}
  one_mem' := by simp [offset_one]
  mul_mem' := by
    intro x y hx hy i
    change ((x.v i + y.v ((perm x.g).symm i) : ℤ) : ZMod 2) = _
    rw [Int.cast_add, hx, hy, Ambient.mul_g, offset_mul]
  inv_mem' := by
    intro x hx i
    change ((-x.v ((perm x.g⁻¹).symm i) : ℤ) : ZMod 2) = _
    rw [Int.cast_neg, hx, Ambient.inv_g, offset_inv, perm_inv]
    rfl

abbrev Gamma := extension

/-- An element in the coset over g, in integral translation coordinates. -/
def element (g : Hol) (x : V) : Gamma :=
  ⟨⟨offset g + 2 • x, g⟩, by
    intro i
    change (((offset g i + 2 * x i) : ℤ) : ZMod 2) = _
    push_cast
    have htwo : (2 : ZMod 2) = 0 := by decide
    simp [htwo]⟩

@[simp] theorem element_g (g : Hol) (x : V) : (element g x).val.g = g := rfl
@[simp] theorem element_v (g : Hol) (x : V) : (element g x).val.v = offset g + 2 • x := rfl

/-- Coordinates in the full translation lattice 2ℤ⁵. -/
def coordinates (x : Gamma) : V := fun i => (x.val.v i - offset x.val.g i) / 2

theorem coordinates_spec (x : Gamma) : x.val.v = offset x.val.g + 2 • coordinates x := by
  ext i
  have h := x.property i
  have hd : (2 : ℤ) ∣ x.val.v i - offset x.val.g i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [h, sub_self]
  change x.val.v i = offset x.val.g i + 2 * ((x.val.v i - offset x.val.g i) / 2)
  omega

theorem element_coordinates (x : Gamma) : element x.val.g (coordinates x) = x := by
  apply Subtype.ext
  apply Ambient.ext
  · exact (coordinates_spec x).symm
  · rfl

@[simp] theorem coordinates_element (g : Hol) (x : V) : coordinates (element g x) = x := by
  ext i
  change (offset g i + 2 * x i - offset g i) / 2 = x i
  omega

/-- Pure translations in the extension, scaled by two. -/
def translation (x : V) : Gamma := element 1 x

@[simp] theorem translation_g (x : V) : (translation x).val.g = 1 := rfl
@[simp] theorem translation_v (x : V) : (translation x).val.v = 2 • x := by
  simp [translation, offset_one]

end ArtinRinf.Dihedral5
