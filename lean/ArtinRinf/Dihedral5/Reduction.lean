/- Reduction of the infinite affine group to its finite translation-class model. -/
import ArtinRinf.Dihedral5.Automorphism
import ArtinRinf.Dihedral5.ActionData
import ArtinRinf.FiniteTwistedClasses

open Matrix
namespace ArtinRinf.Dihedral5

def twist (z x : Gamma) : Gamma := z * x * (phi z)⁻¹

@[simp] theorem twist_g (z x : Gamma) : (twist z x).val.g = conjugate x.val.g z.val.g := by
  simp [twist, conjugate]

theorem twist_v (z x : Gamma) : (twist z x).val.v =
    z.val.v + pact (perm z.val.g) x.val.v -
      pact (perm (conjugate x.val.g z.val.g)) (phi z).val.v := by
  simp only [twist, Subgroup.coe_mul, Subgroup.coe_inv, Ambient.mul_v, Ambient.mul_g,
    Ambient.inv_v, phi_g, conjugate, perm_mul, pact_mul, Aff.pact_neg]
  rfl

theorem defect_mulVec (g : Hol) (x : V) :
    defect g *ᵥ x = x - pact (perm g) (D *ᵥ x) := by
  rw [defect, sub_mulVec, one_mulVec, ← mulVec_mulVec, pmat_mulVec]

lemma pact_smul (g : Hol) (n : ℤ) (x : V) : pact (perm g) (n • x) = n • pact (perm g) x := rfl

lemma pact_nsmul (g : Hol) (n : ℕ) (x : V) : pact (perm g) (n • x) = n • pact (perm g) x := rfl

theorem twist_element (g h : Hol) (x t : V) :
    twist (element h t) (element g x) =
      element (conjugate g h) (pact (perm h) x + twistOffset g h + defect (conjugate g h) *ᵥ t) := by
  apply Subtype.ext
  apply Ambient.ext
  · rw [twist_v, phi_v]
    simp only [element_v, element_g, mulVec_add, mulVec_smul, Aff.pact_add, pact_sub,
      pact_nsmul, defect_mulVec]
    have hshift := twistOffset_spec g h
    -- Group the constant part before using the finite offset certificate.
    calc _        = (offset h + pact (perm h) (offset g) -
            pact (perm (conjugate g h)) (D *ᵥ offset h +
              (displacement - pact (perm h) displacement))) +
          2 • (pact (perm h) x + (t - pact (perm (conjugate g h)) (D *ᵥ t))) := by
            simp only [Aff.pact_add, pact_sub]
            module
      _ = (offset (conjugate g h) + 2 • twistOffset g h) +
          2 • (pact (perm h) x + (t - pact (perm (conjugate g h)) (D *ᵥ t))) := by rw [hshift]
      _ = _ := by module
  · simp

/-- Encode a translation class in its cyclic quotient. -/
def encode (x : Gamma) : State := ⟨x.val.g, (ell x.val.g ⬝ᵥ coordinates x : ℤ)⟩

def liftState (s : State) : Gamma := element s.1 ((s.2.val : ℤ) • unit s.1)

@[simp] theorem encode_element (g : Hol) (x : V) :
    encode (element g x) = ⟨g, (ell g ⬝ᵥ x : ℤ)⟩ := by
  simp only [encode, element_g, coordinates_element]
  rfl

@[simp] theorem encode_liftState (s : State) : encode (liftState s) = s := by
  rcases s with ⟨g, k⟩
  simp only [liftState, encode_element, dotProduct_smul, ell_unit, smul_eq_mul,
    mul_one, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- The integer solution that removes all but the cyclic coordinate. -/
def reducingTranslation (g : Hol) (x : V) : V :=
  -(reduceMatrix g *ᵥ x + ((ell g ⬝ᵥ x) / (modulus g : ℤ)) • reduceVector g)

theorem reduction_identity (g : Hol) (x : V) :
    x + defect g *ᵥ reducingTranslation g x =
      (((ell g ⬝ᵥ x : ℤ) : ZMod (modulus g)).val : ℤ) • unit g := by
  rw [reducingTranslation, mulVec_neg, mulVec_add, mulVec_smul, mulVec_mulVec,
    reduction_matrix, reduction_vector, sub_mulVec, one_mulVec, vecMulVec_mulVec]
  rw [op_smul_eq_smul, ZMod.val_intCast]
  have hdiv := Int.emod_add_mul_ediv (ell g ⬝ᵥ x) (modulus g : ℤ)
  ext i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination -(unit g i) * hdiv

theorem twist_translation (g : Hol) (x t : V) :
    twist (translation t) (element g x) = element g (x + defect g *ᵥ t) := by
  have hc : conjugate g 1 = g := by simp [conjugate]
  have hs : twistOffset g 1 = 0 := by
    revert g
    decide +kernel
  simpa [translation, hc, hs, perm_one] using twist_element g 1 x t

/-- Every element is translation-twisted conjugate to its encoded representative. -/
theorem reduce (x : Gamma) : (twistedSetoid phi.toMonoidHom) x (liftState (encode x)) := by
  refine ⟨translation (reducingTranslation x.val.g (coordinates x)), ?_⟩
  change liftState (encode x) = twist _ x
  conv_rhs => rw [← element_coordinates x]
  simp only [element_g, coordinates_element]
  rw [twist_translation, reduction_identity]
  rfl

end ArtinRinf.Dihedral5
