/-
# Integral lattice fixed-vector criterion

The linear argument is independent of Artin groups and permutation bases.
Choose any integral basis of a lattice; all matrices below are in that basis.
-/
import ArtinRinf.FreeAbelian

open Function Matrix

namespace ArtinRinf

/-! ### The Schur / lattice step (Lemma 3.1) -/

/-- A rational number `q ≠ 0` such that `q^k x` is an integer for all `k` (for some integer
`x ≠ 0`) satisfies `1 ≤ |q|`. -/
lemma one_le_abs_of_pow_mul_int (q : ℚ) (hq : q ≠ 0) (x : ℤ) (hx : x ≠ 0)
    (h : ∀ k : ℕ, ∃ m : ℤ, q ^ k * x = m) : 1 ≤ |q| := by
  by_contra hlt
  push Not at hlt
  have hxpos : (0 : ℚ) < 1 / |(x : ℚ)| := by
    have : (x : ℚ) ≠ 0 := by exact_mod_cast hx
    positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hxpos hlt
  obtain ⟨m, hm⟩ := h k
  have hxabs : (0 : ℚ) < |(x : ℚ)| := by
    have : (x : ℚ) ≠ 0 := by exact_mod_cast hx
    positivity
  have habs : |(m : ℚ)| < 1 := by
    rw [← hm, abs_mul, abs_pow]
    calc |q| ^ k * |(x : ℚ)| < 1 / |(x : ℚ)| * |(x : ℚ)| :=
          mul_lt_mul_of_pos_right hk hxabs
      _ = 1 := by field_simp
  have hm0 : m = 0 := by
    have : |m| < 1 := by exact_mod_cast habs
    exact Int.abs_lt_one_iff.mp this
  rw [hm0, Int.cast_zero] at hm
  have : q ^ k ≠ 0 := pow_ne_zero _ hq
  have : (x : ℚ) ≠ 0 := by exact_mod_cast hx
  exact absurd hm (mul_ne_zero ‹q ^ k ≠ 0› this)

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Clearing denominators: a nonzero rational vector has a nonzero integral multiple. -/
lemma exists_int_multiple (v : T → ℚ) (hv : v ≠ 0) :
    ∃ (D : ℚ) (x : T → ℤ), D ≠ 0 ∧ x ≠ 0 ∧ ∀ i, D * v i = x i := by
  classical
  let D : ℕ := ∏ i, (v i).den
  have hD : (D : ℚ) ≠ 0 := by
    have : D ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (v i).den_nz)
    exact_mod_cast this
  have hint : ∀ i, ∃ m : ℤ, (D : ℚ) * v i = m := by
    intro i
    obtain ⟨k, hk⟩ : (v i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    refine ⟨k * (v i).num, ?_⟩
    rw [hk]
    push_cast
    rw [mul_comm ((v i).den : ℚ) _, mul_assoc, Rat.den_mul_eq_num]
  choose x hx using hint
  refine ⟨(D : ℚ), x, hD, ?_, hx⟩
  intro h0
  apply hv
  ext i
  have := hx i
  rw [h0, Pi.zero_apply, Int.cast_zero] at this
  simpa [hD] using this

lemma castQ_mulVec_cast (N : Matrix T T ℤ) (x : T → ℤ) :
    castQ N *ᵥ (fun i => (x i : ℚ)) = fun i => ((N *ᵥ x) i : ℚ) := castQ_mulVec N x

lemma castQ_mul (M N : Matrix T T ℤ) : castQ (M * N) = castQ M * castQ N :=
  Matrix.map_mul (f := Int.castRingHom ℚ)

lemma castQ_one : castQ (1 : Matrix T T ℤ) = 1 := Matrix.map_one _ (by simp) (by simp)

lemma castQ_pow (N : Matrix T T ℤ) (k : ℕ) : castQ (N ^ k) = castQ N ^ k := by
  induction k with
  | zero => simp [castQ_one]
  | succ k ih => rw [pow_succ, castQ_mul, ih, pow_succ]

/-- **Lemma 3.1 (lattice step).**  If an integer matrix `N` with an integer left inverse has a
rational eigenvector `v ≠ 0` with rational eigenvalue `c`, then `c = ±1`. -/
theorem eigenvalue_eq_one_or_neg_one (N N' : Matrix T T ℤ) (hNN' : N' * N = 1)
    (v : T → ℚ) (hv : v ≠ 0) (c : ℚ) (hc : castQ N *ᵥ v = c • v) : c = 1 ∨ c = -1 := by
  obtain ⟨D, x, hD, hx0, hx⟩ := exists_int_multiple v hv
  have hxv : (fun i => (x i : ℚ)) = D • v := by ext i; simp [← hx i]
  have hcx : castQ N *ᵥ (fun i => (x i : ℚ)) = c • (fun i => (x i : ℚ)) := by
    rw [hxv, mulVec_smul, hc, smul_comm]
  -- `c ≠ 0`
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hcx
    have : castQ N' *ᵥ (castQ N *ᵥ (fun i => (x i : ℚ))) = fun i => (x i : ℚ) := by
      rw [mulVec_mulVec, ← castQ_mul, hNN', castQ_one, one_mulVec]
    rw [hcx, mulVec_zero] at this
    apply hx0; ext i
    have := congrFun this i
    simp only [Pi.zero_apply] at this
    exact_mod_cast this.symm
  -- `N'` acts by `c⁻¹`
  have hcx' : castQ N' *ᵥ (fun i => (x i : ℚ)) = c⁻¹ • (fun i => (x i : ℚ)) := by
    have : castQ N' *ᵥ (castQ N *ᵥ (fun i => (x i : ℚ))) = fun i => (x i : ℚ) := by
      rw [mulVec_mulVec, ← castQ_mul, hNN', castQ_one, one_mulVec]
    rw [hcx, mulVec_smul] at this
    calc castQ N' *ᵥ (fun i => (x i : ℚ))
        = c⁻¹ • (c • castQ N' *ᵥ (fun i => (x i : ℚ))) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • (fun i => (x i : ℚ)) := by rw [this]
  -- powers
  have hpow : ∀ (M : Matrix T T ℤ) (d : ℚ),
      castQ M *ᵥ (fun i => (x i : ℚ)) = d • (fun i => (x i : ℚ)) →
      ∀ k : ℕ, ∀ i, ∃ m : ℤ, d ^ k * x i = m := by
    intro M d hd k i
    have : castQ (M ^ k) *ᵥ (fun i => (x i : ℚ)) = d ^ k • (fun i => (x i : ℚ)) := by
      rw [castQ_pow]
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← mulVec_mulVec, hd, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
    refine ⟨(M ^ k *ᵥ x) i, ?_⟩
    have h2 := congrFun this i
    rw [castQ_mulVec_cast] at h2
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    exact h2.symm
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (funext h)
  have h1 : 1 ≤ |c| := one_le_abs_of_pow_mul_int c hc0 (x i) hi (fun k => hpow N c hcx k i)
  have h2 : 1 ≤ |c⁻¹| := one_le_abs_of_pow_mul_int c⁻¹ (inv_ne_zero hc0) (x i) hi
    (fun k => hpow N' c⁻¹ hcx' k i)
  have habs : |c| = 1 := by
    rw [abs_inv] at h2
    have hpos : 0 < |c| := abs_pos.mpr hc0
    have : |c| ≤ 1 := by
      have := (one_le_inv₀ hpos).mp h2
      exact this
    exact le_antisymm this h1
  rcases abs_eq (zero_le_one) |>.mp habs with h | h
  · exact Or.inl h
  · exact Or.inr h

/-! ### Stable and exchanged subspaces in an arbitrary lattice basis -/

def ScalarOn (N : Matrix T T ℤ) (U : Submodule ℚ (T → ℚ)) : Prop :=
  ∃ c : ℚ, ∀ u ∈ U, castQ N *ᵥ u = c • u

/-- Sign witnesses after factoring a holonomy twist as `Q i * N`.
No permutation action or Artin group is required. -/
def LatticeSignWitness {ι : Type*} (N : Matrix T T ℤ) (Q : ι → Matrix T T ℚ) : Prop :=
  (∃ U : Submodule ℚ (T → ℚ), ScalarOn N U ∧
    ∀ ε : ℚ, (ε = 1 ∨ ε = -1) →
      ∃ i v, v ∈ U ∧ v ≠ 0 ∧ Q i *ᵥ v = ε • v) ∨
  (∃ U₁ U₂ : Submodule ℚ (T → ℚ), ScalarOn N U₁ ∧ ScalarOn N U₂ ∧
    ∀ ε : ℚ, (ε = 1 ∨ ε = -1) →
      ∃ i v, v ∈ U₁ ∧ v ≠ 0 ∧ Q i *ᵥ v ∈ U₂ ∧
        Q i *ᵥ (Q i *ᵥ v) = ε • v ∧ Q i *ᵥ v ≠ v ∧ Q i *ᵥ v ≠ -v)

/-- The common fixed-vector mechanism, valid in any integral lattice basis. -/
theorem exists_fixed_of_lattice_sign_witness {ι : Type*}
    (N N' : Matrix T T ℤ) (hNN' : N' * N = 1) (Q : ι → Matrix T T ℚ)
    (hinj : ∀ i, Injective (fun v => Q i *ᵥ v)) (hW : LatticeSignWitness N Q) :
    ∃ i v, v ≠ 0 ∧ (Q i * castQ N) *ᵥ v = v := by
  have hscal : ∀ U : Submodule ℚ (T → ℚ), ScalarOn N U → ∀ v ∈ U, v ≠ 0 →
      ∃ c : ℚ, (c = 1 ∨ c = -1) ∧ ∀ u ∈ U, castQ N *ᵥ u = c • u := by
    intro U hU v hvU hv0
    obtain ⟨c, hc⟩ := hU
    exact ⟨c, eigenvalue_eq_one_or_neg_one N N' hNN' v hv0 c (hc v hvU), hc⟩
  rcases hW with ⟨U, hU, hWit⟩ | ⟨U₁, U₂, hU₁, hU₂, hWit⟩
  · obtain ⟨i0, v0, hv0U, hv00, -⟩ := hWit 1 (Or.inl rfl)
    obtain ⟨c, hc1, hc⟩ := hscal U hU v0 hv0U hv00
    obtain ⟨i, v, hvU, hv0, hv⟩ := hWit c hc1
    refine ⟨i, v, hv0, ?_⟩
    rw [← mulVec_mulVec, hc v hvU, mulVec_smul, hv, smul_smul]
    rcases hc1 with rfl | rfl <;> norm_num
  · obtain ⟨i0, v0, hv0U, hv00, h01, -, -, -⟩ := hWit 1 (Or.inl rfl)
    obtain ⟨c₁, hc₁1, hc₁⟩ := hscal U₁ hU₁ v0 hv0U hv00
    have hQv0 : Q i0 *ᵥ v0 ≠ 0 := by
      intro h0
      exact hv00 (hinj i0 (by simpa using h0))
    obtain ⟨c₂, hc₂1, hc₂⟩ := hscal U₂ hU₂ _ h01 hQv0
    have hε : c₁ * c₂ = 1 ∨ c₁ * c₂ = -1 := by
      rcases hc₁1 with rfl | rfl <;> rcases hc₂1 with rfl | rfl <;> norm_num
    obtain ⟨i, v, hvU, hv0, hQU, hQ2, hne1, hne2⟩ := hWit (c₁ * c₂) hε
    set M := Q i * castQ N with hM
    have hMv : M *ᵥ v = c₁ • (Q i *ᵥ v) := by
      rw [hM, ← mulVec_mulVec, hc₁ v hvU, mulVec_smul]
    have hM2 : M *ᵥ (M *ᵥ v) = v := by
      rw [hMv, mulVec_smul, hM, ← mulVec_mulVec, hc₂ _ hQU, mulVec_smul, hQ2,
        smul_smul, smul_smul]
      rcases hc₁1 with rfl | rfl <;> rcases hc₂1 with rfl | rfl <;> norm_num
    refine ⟨i, v + M *ᵥ v, ?_, ?_⟩
    · rw [hMv]
      rcases hc₁1 with rfl | rfl
      · rw [one_smul]
        intro h
        apply hne2
        rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
        exact h
      · intro h
        rw [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h
        exact hne1 h.symm
    · change M *ᵥ (v + M *ᵥ v) = v + M *ᵥ v
      rw [mulVec_add, hM2, add_comm]

/-- A fixed vector on an invariant finite-index free abelian subgroup forces
infinite Reidemeister number, in any integral basis. -/
theorem reidemeister_eq_top_of_lattice_matrix {G : Type*} [Group G]
    (φ : G →* G) (L : Subgroup G) [L.FiniteIndex]
    (hL : ∀ x ∈ L, φ x ∈ L) (e : L ≃* Multiplicative (T → ℤ))
    (D : Matrix T T ℤ)
    (hD : ∀ x : L, e (restrictEnd φ L hL x) = matEnd D (e x))
    (v : T → ℚ) (hv : v ≠ 0) (hfix : castQ D *ᵥ v = v) : reidemeister φ = ⊤ := by
  apply reidemeister_eq_top_of_restrict φ L hL
  rw [reidemeister_eq_of_mulEquiv (restrictEnd φ L hL) (matEnd D) e hD]
  exact reidemeister_matEnd_eq_top D v hv hfix

end ArtinRinf
