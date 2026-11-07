/-
# Reidemeister numbers on `ℤ^T`  (paper, Lemma 2.1(b), the part used)

If `B ∈ M_T(ℤ)` has eigenvalue `1` over `ℚ` (equivalently `det (B - 1) = 0`), then the endomorphism
`x ↦ B x` of `ℤ^T` has infinitely many twisted conjugacy classes.

The proof: a fixed vector over `ℚ` gives a fixed *covector* `w` (`wB = w`), since
`det (B - 1) = 0`. The functional `x ↦ w ⬝ x` is constant on twisted classes
(`y = z + x - Bz`), and takes infinitely many values.
-/
import ArtinRinf.Reidemeister

open Function Matrix

namespace ArtinRinf

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The endomorphism `x ↦ B x` of `ℤ^T`, written multiplicatively. -/
def matEnd (B : Matrix T T ℤ) : Multiplicative (T → ℤ) →* Multiplicative (T → ℤ) :=
  AddMonoidHom.toMultiplicative (Matrix.mulVecLin B).toAddMonoidHom

@[simp] lemma matEnd_apply (B : Matrix T T ℤ) (x : Multiplicative (T → ℤ)) :
    matEnd B x = Multiplicative.ofAdd (B *ᵥ x.toAdd) := rfl

/-- The rational matrix of an integer matrix. -/
abbrev castQ (B : Matrix T T ℤ) : Matrix T T ℚ := B.map (Int.cast : ℤ → ℚ)

lemma castQ_mulVec (B : Matrix T T ℤ) (x : T → ℤ) :
    castQ B *ᵥ (fun i => (x i : ℚ)) = fun i => ((B *ᵥ x) i : ℚ) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- Lemma 2.1(b), the part used: if `det (B - 1) = 0` over `ℚ` then `R(B) = ∞`. -/
theorem reidemeister_matEnd_eq_top_of_det (B : Matrix T T ℤ) (hdet : (castQ B - 1).det = 0) :
    reidemeister (matEnd B) = ⊤ := by
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hwB : w ᵥ* castQ B = w := by
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero] at hw
    exact hw
  -- the invariant functional
  let ℓ : Multiplicative (T → ℤ) → ℚ := fun x => w ⬝ᵥ (fun i => ((x.toAdd i : ℤ) : ℚ))
  have hℓ : ∀ x y, (twistedSetoid (matEnd B)) x y → ℓ x = ℓ y := by
    rintro x y ⟨z, rfl⟩
    simp only [ℓ, matEnd_apply, toAdd_mul, toAdd_inv, toAdd_ofAdd, Pi.add_apply, Pi.neg_apply,
      Int.cast_add, Int.cast_neg]
    have h1 := castQ_mulVec B z.toAdd
    have key : w ⬝ᵥ (fun i => ((B *ᵥ z.toAdd) i : ℚ)) = w ⬝ᵥ (fun i => (z.toAdd i : ℚ)) := by
      rw [← h1, Matrix.dotProduct_mulVec, hwB]
    have e : (fun i => ((z.toAdd i : ℚ) + (x.toAdd i : ℚ)) + -((B *ᵥ z.toAdd) i : ℚ))
        = (fun i => (z.toAdd i : ℚ)) + (fun i => (x.toAdd i : ℚ))
          - (fun i => ((B *ᵥ z.toAdd) i : ℚ)) := by
      ext i; simp [sub_eq_add_neg]
    rw [e, dotProduct_sub, dotProduct_add, key]
    ring
  let L : TwistedClasses (matEnd B) → ℚ := Quotient.lift ℓ hℓ
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw0 (funext h)
  -- `n ↦ [n e_j]` is injective
  let g : ℤ → TwistedClasses (matEnd B) :=
    fun n => Quotient.mk'' (Multiplicative.ofAdd (Pi.single j n))
  have hg : Injective g := by
    intro n m hnm
    have := congrArg L hnm
    simp only [L, g, Quotient.lift_mk, ℓ, toAdd_ofAdd] at this
    change (w ⬝ᵥ fun i => ((Pi.single j n : T → ℤ) i : ℚ))
      = (w ⬝ᵥ fun i => ((Pi.single j m : T → ℤ) i : ℚ)) at this
    have e : ∀ k : ℤ, (fun i => ((Pi.single j k : T → ℤ) i : ℚ)) = Pi.single j (k : ℚ) := by
      intro k; ext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [Pi.single_apply, hi]
    rw [e, e, dotProduct_single, dotProduct_single] at this
    exact_mod_cast mul_left_cancel₀ hj this
  rw [reidemeister_eq_top_iff]
  exact Infinite.of_injective g hg

/-- Lemma 2.1(b), the part used: if `B` has a nonzero rational fixed vector then `R(B) = ∞`. -/
theorem reidemeister_matEnd_eq_top (B : Matrix T T ℤ) (v : T → ℚ) (hv : v ≠ 0)
    (hBv : castQ B *ᵥ v = v) : reidemeister (matEnd B) = ⊤ := by
  apply reidemeister_matEnd_eq_top_of_det
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  exact ⟨v, hv, by rw [Matrix.sub_mulVec, Matrix.one_mulVec, hBv, sub_self]⟩

end ArtinRinf
