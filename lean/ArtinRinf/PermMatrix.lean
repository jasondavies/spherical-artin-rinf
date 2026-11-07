/-
# Permutation matrices with the convention `ρ(σ) e_r = e_{σ r}`
-/
import Mathlib

open Matrix

namespace ArtinRinf

variable {T : Type*}

/-- The permutation action on functions: `(σ • v) i = v (σ⁻¹ i)`, so that `e_r ↦ e_{σ r}`. -/
def pact {R : Type*} (σ : Equiv.Perm T) (v : T → R) : T → R := fun i => v (σ.symm i)

@[simp] lemma pact_apply {R : Type*} (σ : Equiv.Perm T) (v : T → R) (i : T) :
    pact σ v i = v (σ.symm i) := rfl

lemma pact_mul {R : Type*} (σ τ : Equiv.Perm T) (v : T → R) :
    pact (σ * τ) v = pact σ (pact τ v) := by
  ext i; simp [pact, Equiv.Perm.mul_def]

@[simp] lemma pact_one {R : Type*} (v : T → R) : pact (1 : Equiv.Perm T) v = v := rfl

variable [Fintype T] [DecidableEq T]

/-- The permutation matrix of `σ`, with `pmat σ *ᵥ e_r = e_{σ r}`. -/
def pmat (R : Type*) [Zero R] [One R] (σ : Equiv.Perm T) : Matrix T T R :=
  Matrix.of fun i j => if i = σ j then 1 else 0

lemma pmat_mulVec {R : Type*} [NonAssocSemiring R] (σ : Equiv.Perm T) (v : T → R) :
    pmat R σ *ᵥ v = pact σ v := by
  ext i
  simp only [pmat, mulVec, dotProduct, of_apply, ite_mul, one_mul, zero_mul, pact_apply]
  have : ∀ j, (i = σ j) ↔ (j = σ.symm i) := fun j => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp_rw [this]
  simp

lemma pmat_mul {R : Type*} [Semiring R] (σ τ : Equiv.Perm T) :
    pmat R (σ * τ) = pmat R σ * pmat R τ := by
  apply Matrix.ext_of_mulVec_single
  intro k
  rw [← Matrix.mulVec_mulVec, pmat_mulVec, pmat_mulVec, pmat_mulVec, pact_mul]

@[simp] lemma pmat_one {R : Type*} [NonAssocSemiring R] : pmat R (1 : Equiv.Perm T) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [pmat, Matrix.one_apply, h]

lemma pmat_inv_mul {R : Type*} [Semiring R] (σ : Equiv.Perm T) :
    pmat R σ⁻¹ * pmat R σ = 1 := by
  rw [← pmat_mul, inv_mul_cancel, pmat_one]

lemma pmat_mul_inv {R : Type*} [Semiring R] (σ : Equiv.Perm T) :
    pmat R σ * pmat R σ⁻¹ = 1 := by
  rw [← pmat_mul, mul_inv_cancel, pmat_one]

lemma map_pmat {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S)
    (σ : Equiv.Perm T) : (pmat R σ).map f = pmat S σ := by
  ext i j
  simp only [pmat, map_apply, of_apply]
  split_ifs <;> simp

lemma pact_single_one {R : Type*} [Zero R] [One R] (σ : Equiv.Perm T) (r : T) :
    pact σ (Pi.single r (1 : R)) = Pi.single (σ r) 1 := by
  ext i
  simp only [pact_apply, Pi.single_apply]
  congr 1
  apply propext
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

end ArtinRinf
