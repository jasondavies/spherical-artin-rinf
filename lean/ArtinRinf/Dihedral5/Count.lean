/- The finite action classifies all twisted classes in the infinite extension. -/
import ArtinRinf.Dihedral5.Reduction

open Matrix
namespace ArtinRinf.Dihedral5

lemma cast_dot_congr {n : ℕ} (a b x : V)
    (h : ∀ i, (a i : ZMod n) = (b i : ZMod n)) :
    ((a ⬝ᵥ x : ℤ) : ZMod n) = ((b ⬝ᵥ x : ℤ) : ZMod n) := by
  simp only [dotProduct, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [h]

lemma ell_twist (g h : Hol) (x t : V) :
    ((ell (conjugate g h) ⬝ᵥ
      (pact (perm h) x + twistOffset g h + defect (conjugate g h) *ᵥ t) : ℤ) :
        ZMod (modulus (conjugate g h))) =
    ((slope g h * (ell g ⬝ᵥ x) + intercept g h : ℤ) : ZMod (modulus (conjugate g h))) := by
  have ht := cast_dot_congr _ (fun i => slope g h * ell g i) x (ell_transport g h)
  have hd := cast_dot_congr _ (0 : V) t (fun i => by simpa using ell_defect (conjugate g h) i)
  rw [← pmat_mulVec (perm h) x, dotProduct_add, dotProduct_add,
    dotProduct_mulVec, dotProduct_mulVec]
  rw [Int.cast_add, Int.cast_add, ht, ell_shift, hd]
  simp only [zero_dotProduct, Int.cast_zero, add_zero, Int.cast_add]
  congr 1
  exact congrArg (fun z : ℤ => (z : ZMod (modulus (conjugate g h))))
    (smul_dotProduct (slope g h) (ell g) x)

theorem encode_twist_element (g h : Hol) (x t : V) :
    encode (twist (element h t) (element g x)) = move h (encode (element g x)) := by
  rw [twist_element, encode_element, encode_element]
  unfold move
  congr 1
  change _ = ((slope g h * (((ell g ⬝ᵥ x : ℤ) : ZMod (modulus g)).val : ℤ) +
    intercept g h : ℤ) : ZMod (modulus (conjugate g h)))
  rw [ell_twist]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  rw [modulus_conjugate]
  rw [ZMod.natCast_zmod_val]

theorem encode_twist (z x : Gamma) : encode (twist z x) = move z.val.g (encode x) := by
  obtain ⟨g, u, rfl⟩ : ∃ g u, x = element g u :=
    ⟨x.val.g, coordinates x, (element_coordinates x).symm⟩
  obtain ⟨h, t, rfl⟩ : ∃ h t, z = element h t :=
    ⟨z.val.g, coordinates z, (element_coordinates z).symm⟩
  exact encode_twist_element g h u t

theorem move_relation (h : Hol) (s : State) :
    (twistedSetoid phi.toMonoidHom) (liftState s) (liftState (move h s)) := by
  have h₁ : (twistedSetoid phi.toMonoidHom) (liftState s)
      (twist (element h 0) (liftState s)) := ⟨element h 0, rfl⟩
  have h₂ := reduce (twist (element h 0) (liftState s))
  rw [encode_twist, encode_liftState, element_g] at h₂
  exact (twistedSetoid phi.toMonoidHom).trans h₁ h₂

/-- A complete classification, not merely a count of a finite surrogate. -/
def classification : TwistedClassification phi.toMonoidHom 18 where
  label x := label (encode x)
  representative i := liftState (representative i)
  invariant := by
    rintro x y ⟨z, rfl⟩
    change label (encode x) = label (encode (twist z x))
    rw [encode_twist, label_move]
  complete x := by
    have h := move_relation (conjugator (encode x)) (encode x)
    rw [move_representative] at h
    exact (twistedSetoid phi.toMonoidHom).trans (reduce x) h
  label_representative i := by rw [encode_liftState, label_representative]

/-- The explicit affine automorphism has exactly eighteen twisted classes. -/
theorem reidemeister_phi : reidemeisterAut phi = 18 := classification.reidemeister_eq

end ArtinRinf.Dihedral5
