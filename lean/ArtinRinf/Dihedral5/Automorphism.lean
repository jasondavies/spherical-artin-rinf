/- The extension-compatible I₂(5) automorphism, with an explicit inverse. -/
import ArtinRinf.Dihedral5.Model
import ArtinRinf.Dihedral5.Matrices

open Matrix
namespace ArtinRinf.Dihedral5

lemma pact_sub (g : Hol) (x y : V) :
    pact (perm g) (x - y) = pact (perm g) x - pact (perm g) y := rfl

theorem D_pact (g : Hol) (x : V) : D *ᵥ pact (perm g) x = pact (perm g) (D *ᵥ x) := by
  simp only [← pmat_mulVec, mulVec_mulVec, D_comm]

def forward (x : Gamma) : Gamma :=
  element x.val.g (D *ᵥ coordinates x + correction x.val.g)

def backward (x : Gamma) : Gamma :=
  element x.val.g (Dinv *ᵥ coordinates x + invCorrection x.val.g)

@[simp] theorem forward_g (x : Gamma) : (forward x).val.g = x.val.g := rfl
@[simp] theorem backward_g (x : Gamma) : (backward x).val.g = x.val.g := rfl

/-- The formula is precisely conjugation by `(displacement,D)` in the ambient affine group. -/
theorem forward_v (x : Gamma) : (forward x).val.v =
    D *ᵥ x.val.v + (displacement - pact (perm x.val.g) displacement) := by
  change offset x.val.g + 2 • (D *ᵥ coordinates x + correction x.val.g) = _
  rw [coordinates_spec x, mulVec_add, mulVec_smul]
  rw [smul_add]
  calc offset x.val.g + (2 • (D *ᵥ coordinates x) + 2 • correction x.val.g)
      = 2 • (D *ᵥ coordinates x) + (offset x.val.g + 2 • correction x.val.g) := by abel
    _ = 2 • (D *ᵥ coordinates x) +
        (D *ᵥ offset x.val.g + (displacement - pact (perm x.val.g) displacement)) := by
          rw [← correction_spec]
    _ = _ := by abel

@[simp] theorem backward_forward (x : Gamma) : backward (forward x) = x := by
  unfold backward forward
  simp only [element_g, coordinates_element, mulVec_add, mulVec_mulVec, Dinv_D, one_mulVec]
  rw [add_assoc, invCorrection_spec, add_zero]
  exact element_coordinates x

@[simp] theorem forward_backward (x : Gamma) : forward (backward x) = x := by
  unfold forward backward
  simp only [element_g, coordinates_element, mulVec_add, mulVec_mulVec, D_Dinv, one_mulVec]
  rw [add_assoc, correction_inv_spec, add_zero]
  exact element_coordinates x

theorem forward_mul (x y : Gamma) : forward (x * y) = forward x * forward y := by
  apply Subtype.ext
  apply Ambient.ext
  · change (forward (x * y)).val.v = ((forward x).val * (forward y).val).v
    rw [forward_v, Ambient.mul_v, forward_v, forward_v, forward_g]
    change D *ᵥ (x.val.v + pact (perm x.val.g) y.val.v) +
      (displacement - pact (perm (x.val.g * y.val.g)) displacement) = _
    rw [mulVec_add, D_pact, perm_mul, pact_mul]
    simp only [Aff.pact_add, pact_sub]
    abel
  · rfl

/-- The automorphism of the actual parity extension; no splitting is assumed. -/
def phi : Gamma ≃* Gamma where
  toFun := forward
  invFun := backward
  left_inv := backward_forward
  right_inv := forward_backward
  map_mul' := forward_mul

@[simp] theorem phi_g (x : Gamma) : (phi x).val.g = x.val.g := rfl

theorem phi_v (x : Gamma) : (phi x).val.v =
    D *ᵥ x.val.v + (displacement - pact (perm x.val.g) displacement) := forward_v x

end ArtinRinf.Dihedral5
