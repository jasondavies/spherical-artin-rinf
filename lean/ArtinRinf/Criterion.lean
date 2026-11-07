/-
# The abstract Artin-group criterion (see lean/DIRECT_PROOF.md)

Setting.
* `A` a group, `P ≤ A` a characteristic subgroup of finite index.
* `T` a finite set, `ρ : A →* Perm T`.
* `E : PermModuleIso P ρ`: an isomorphism `P^ab ≃ ℤ^T` under which conjugation by `a ∈ A`
  becomes the permutation `ρ a` of coordinates (no signs).  For Artin groups this is
  Proposition 2.4 of the paper (Brieskorn).
* A rational subspace `U ≤ ℚ^T` such that *every* `ℚ`-matrix commuting with all `ρ a` acts on `U`
  by a scalar (`CommScalar ρ U`).  This is exactly what the paper uses of a "good constituent".

Conclusion: if the automorphism of `ρ(A)` induced by `φ ∈ Aut A` is realised by a permutation `π`
of `T` satisfying the witness condition (stable or swap case), then `R(φ) = ∞`.
-/
import ArtinRinf.LatticeCriterion
import ArtinRinf.PermMatrix

open Function Matrix

namespace ArtinRinf

variable {A : Type*} [Group A]

/-! ### Conjugation on a normal subgroup and restriction of automorphisms -/

/-- Conjugation by `a` on the normal subgroup `P`. -/
def conjP (P : Subgroup A) [P.Normal] (a : A) : P →* P :=
  restrictEnd (MulAut.conj a).toMonoidHom P (fun x hx => Subgroup.Normal.conj_mem ‹_› x hx a)

@[simp] lemma conjP_coe (P : Subgroup A) [P.Normal] (a : A) (p : P) :
    ((conjP P a p : P) : A) = a * p * a⁻¹ := rfl

lemma char_mem (P : Subgroup A) [hP : P.Characteristic] (φ : A ≃* A) {x : A} (hx : x ∈ P) :
    φ x ∈ P :=
  (Subgroup.characteristic_iff_le_comap.mp hP φ) hx

/-- The restriction of an automorphism to a characteristic subgroup. -/
def autP (P : Subgroup A) [P.Characteristic] (φ : A ≃* A) : P →* P :=
  restrictEnd φ.toMonoidHom P (fun _ hx => char_mem P φ hx)

@[simp] lemma autP_coe (P : Subgroup A) [P.Characteristic] (φ : A ≃* A) (p : P) :
    ((autP P φ p : P) : A) = φ p := rfl

/-! ### The equivariant identification `P^ab ≅ ℤ^T` -/

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- An isomorphism `P^ab ≅ ℤ^T` (written multiplicatively) under which conjugation by `a ∈ A`
acts by the permutation `ρ a` of coordinates. -/
structure PermModuleIso (P : Subgroup A) [P.Normal] (ρ : A →* Equiv.Perm T) where
  /-- the isomorphism -/
  e : Abelianization P ≃* Multiplicative (T → ℤ)
  /-- equivariance -/
  equivariant : ∀ (a : A) (p : P),
    (e (Abelianization.of (conjP P a p))).toAdd = pact (ρ a) (e (Abelianization.of p)).toAdd

section MPhi

variable {P : Subgroup A} [P.Characteristic] {ρ : A →* Equiv.Perm T} (E : PermModuleIso P ρ)

/-- The automorphism of `ℤ^T` induced by `φ` (as an additive map). -/
def Mhom (φ : A ≃* A) : (T → ℤ) →+ (T → ℤ) where
  toFun x := (E.e (Abelianization.map (autP P φ) (E.e.symm (Multiplicative.ofAdd x)))).toAdd
  map_zero' := by simp
  map_add' x y := by
    simp only [ofAdd_add, map_mul, toAdd_mul]

/-- The integer matrix `M_φ` of the automorphism of `H₁(P) ≅ ℤ^T` induced by `φ`. -/
def Mmat (φ : A ≃* A) : Matrix T T ℤ := LinearMap.toMatrix' (Mhom E φ).toIntLinearMap

lemma Mmat_mulVec (φ : A ≃* A) (x : T → ℤ) : Mmat E φ *ᵥ x = Mhom E φ x := by
  rw [Mmat, LinearMap.toMatrix'_mulVec]; rfl

lemma Mhom_of (φ : A ≃* A) (p : P) :
    Mhom E φ (E.e (Abelianization.of p)).toAdd = (E.e (Abelianization.of (autP P φ p))).toAdd := by
  simp [Mhom]

/-- every vector of `ℤ^T` comes from an element of `P` -/
lemma exists_of (x : T → ℤ) : ∃ p : P, (E.e (Abelianization.of p)).toAdd = x := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective _ (E.e.symm (Multiplicative.ofAdd x))
  refine ⟨y, ?_⟩
  change (E.e (QuotientGroup.mk' _ y)).toAdd = x
  rw [hy]; simp

/-- Matrices over `ℤ` are determined by their action on `ℤ^T`. -/
lemma mat_ext {M N : Matrix T T ℤ} (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N :=
  Matrix.ext_of_mulVec_single (fun _ => h _)

/-- Corollary 2.5, first part: `M_φ ρ(a) = ρ(φ a) M_φ`. -/
lemma Mmat_pmat (φ : A ≃* A) (a : A) :
    Mmat E φ * pmat ℤ (ρ a) = pmat ℤ (ρ (φ a)) * Mmat E φ := by
  apply mat_ext
  intro x
  obtain ⟨p, rfl⟩ := exists_of E x
  rw [← mulVec_mulVec, ← mulVec_mulVec, pmat_mulVec, pmat_mulVec, Mmat_mulVec, Mmat_mulVec,
    ← E.equivariant, Mhom_of, Mhom_of, ← E.equivariant]
  congr 3
  apply Subtype.ext
  simp [mul_assoc]

/-- Corollary 2.5, second part: `M_{ι_a ∘ φ} = ρ(a) M_φ`. -/
lemma Mmat_conj (φ : A ≃* A) (a : A) :
    Mmat E (φ.trans (MulAut.conj a)) = pmat ℤ (ρ a) * Mmat E φ := by
  apply mat_ext
  intro x
  obtain ⟨p, rfl⟩ := exists_of E x
  rw [← mulVec_mulVec, pmat_mulVec, Mmat_mulVec, Mmat_mulVec, Mhom_of, Mhom_of, ← E.equivariant]
  congr 3

/-- Functoriality: `M_{ψ ∘ φ} = M_ψ M_φ`. -/
lemma Mmat_trans (φ ψ : A ≃* A) : Mmat E (φ.trans ψ) = Mmat E ψ * Mmat E φ := by
  apply mat_ext
  intro x
  obtain ⟨p, rfl⟩ := exists_of E x
  rw [← mulVec_mulVec, Mmat_mulVec, Mmat_mulVec, Mhom_of, Mmat_mulVec, Mhom_of, Mhom_of]
  rfl

lemma Mmat_refl : Mmat E (MulEquiv.refl A) = 1 := by
  apply mat_ext
  intro x
  obtain ⟨p, rfl⟩ := exists_of E x
  rw [Mmat_mulVec, Mhom_of, one_mulVec]
  rfl

lemma Mmat_symm_mul (φ : A ≃* A) : Mmat E φ.symm * Mmat E φ = 1 := by
  rw [← Mmat_trans, MulEquiv.self_trans_symm, Mmat_refl]

/-- **Reduction to linear algebra.**  If `M_φ` has a nonzero rational fixed vector, then
`R(φ) = ∞`.  (Lemma 2.1 (b), (a), (d) and Proposition 2.4.) -/
theorem reidemeister_eq_top_of_fixed [P.FiniteIndex] (φ : A ≃* A) (v : T → ℚ) (hv : v ≠ 0)
    (hfix : castQ (Mmat E φ) *ᵥ v = v) : reidemeisterAut φ = ⊤ := by
  -- `R` on `ℤ^T`
  have h1 : reidemeister (matEnd (Mmat E φ)) = ⊤ := reidemeister_matEnd_eq_top _ v hv hfix
  -- transport to `P^ab`
  have h2 : reidemeister (Abelianization.map (autP P φ)) = ⊤ := by
    rw [reidemeister_eq_of_mulEquiv (Abelianization.map (autP P φ)) (matEnd (Mmat E φ)) E.e]
    · exact h1
    · intro y
      apply Multiplicative.toAdd.injective
      rw [matEnd_apply, toAdd_ofAdd, Mmat_mulVec]
      simp [Mhom]
  -- `R(φ|_P) ≥ R(φ^ab)`
  have h3 : reidemeister (autP P φ) = ⊤ := by
    have := reidemeister_abelianization_le (autP P φ)
    rw [h2, top_le_iff] at this
    exact this
  -- finite index
  exact reidemeister_eq_top_of_restrict φ.toMonoidHom P (fun _ hx => char_mem P φ hx) h3

end MPhi

/-! ### Good constituents and witnesses -/

/-- `U` is a "good constituent" in the sense used by the proof: every rational matrix commuting
with `ρ(A)` acts on `U` as a scalar. -/
def CommScalar (ρ : A →* Equiv.Perm T) (U : Submodule ℚ (T → ℚ)) : Prop :=
  ∀ N : Matrix T T ℚ, (∀ a, N * pmat ℚ (ρ a) = pmat ℚ (ρ a) * N) →
    ∃ c : ℚ, ∀ u ∈ U, N *ᵥ u = c • u

/-- Stable case (i) of the Artin-group criterion (see lean/DIRECT_PROOF.md) for the permutation `π`: for each `ε = ±1` there are `h ∈ ρ(A)`
and `0 ≠ v ∈ U` with `h π v = ε v`. -/
def StableWitness (ρ : A →* Equiv.Perm T) (U : Submodule ℚ (T → ℚ)) (π : Equiv.Perm T) : Prop :=
  ∀ ε : ℚ, (ε = 1 ∨ ε = -1) →
    ∃ a : A, ∃ v ∈ U, v ≠ 0 ∧ pmat ℚ (ρ a * π) *ᵥ v = ε • v

/-- Swap case (ii) of the Artin-group criterion (see lean/DIRECT_PROOF.md) for the permutation `π`, in the form used by the proof: for each
`ε = ±1` there are `h ∈ ρ(A)` and `0 ≠ v ∈ U₁` with `hπ v ∈ U₂`, `(hπ)² v = ε v`, and
`hπ v ≠ ±v`.  (The last condition replaces the use of `U₁ ∩ U₂ = 0` in the paper.) -/
def SwapWitness (ρ : A →* Equiv.Perm T) (U₁ U₂ : Submodule ℚ (T → ℚ)) (π : Equiv.Perm T) :
    Prop :=
  ∀ ε : ℚ, (ε = 1 ∨ ε = -1) →
    ∃ a : A, ∃ v ∈ U₁, v ≠ 0 ∧ pmat ℚ (ρ a * π) *ᵥ v ∈ U₂ ∧
      pmat ℚ (ρ a * π) *ᵥ (pmat ℚ (ρ a * π) *ᵥ v) = ε • v ∧
      pmat ℚ (ρ a * π) *ᵥ v ≠ v ∧ pmat ℚ (ρ a * π) *ᵥ v ≠ -v

/-- The witness condition for `π`: stable case with some good `U`, or swap case with some good
`U₁`, `U₂`. -/
def Witness (ρ : A →* Equiv.Perm T) (π : Equiv.Perm T) : Prop :=
  (∃ U, CommScalar ρ U ∧ StableWitness ρ U π) ∨
    (∃ U₁ U₂, CommScalar ρ U₁ ∧ CommScalar ρ U₂ ∧ SwapWitness ρ U₁ U₂ π)

/-- the inner-coset reduction: the witness condition for `π` implies it for `ρ(g) π`. -/
lemma Witness.mul_left {ρ : A →* Equiv.Perm T} {π : Equiv.Perm T} (h : Witness ρ π) (g : A) :
    Witness ρ (ρ g * π) := by
  have key : ∀ a : A, ρ (a * g⁻¹) * (ρ g * π) = ρ a * π := by
    intro a; simp [mul_assoc]
  rcases h with ⟨U, hU, hW⟩ | ⟨U₁, U₂, hU₁, hU₂, hW⟩
  · refine Or.inl ⟨U, hU, ?_⟩
    intro ε hε
    obtain ⟨a, v, hvU, hv0, hv⟩ := hW ε hε
    exact ⟨a * g⁻¹, v, hvU, hv0, by rw [key]; exact hv⟩
  · refine Or.inr ⟨U₁, U₂, hU₁, hU₂, ?_⟩
    intro ε hε
    obtain ⟨a, v, hvU, hv0, h1, h2, h3, h4⟩ := hW ε hε
    exact ⟨a * g⁻¹, v, hvU, hv0, by rw [key]; exact h1, by rw [key]; exact h2,
      by rw [key]; exact h3, by rw [key]; exact h4⟩

/-! ### the Artin-group criterion (see lean/DIRECT_PROOF.md) -/

section Main

variable {P : Subgroup A} [P.Characteristic] [P.FiniteIndex] {ρ : A →* Equiv.Perm T}
  (E : PermModuleIso P ρ)

lemma castQ_pmat (σ : Equiv.Perm T) : castQ (pmat ℤ σ) = pmat ℚ σ := map_pmat (Int.castRingHom ℚ) σ

/-- `R` is invariant under composing with an inner automorphism (as `MulEquiv`s). -/
lemma reidemeisterAut_conj (φ : A ≃* A) (a : A) :
    reidemeisterAut (φ.trans (MulAut.conj a)) = reidemeisterAut φ := by
  rw [reidemeisterAut, reidemeisterAut, ← reidemeister_inner_comp φ.toMonoidHom a]
  rfl

include E in
/-- **the Artin-group criterion (see lean/DIRECT_PROOF.md)** for a single automorphism `φ`: if `π ρ(a) π⁻¹ = ρ(φ a)` for all `a`, and the
witness condition holds for `π`, then `R(φ) = ∞`. -/
theorem reidemeister_eq_top_of_witness (φ : A ≃* A) (π : Equiv.Perm T)
    (hπ : ∀ a, ρ (φ a) = π * ρ a * π⁻¹) (hW : Witness ρ π) : reidemeisterAut φ = ⊤ := by
  -- `N = π⁻¹ M_φ` commutes with `ρ(A)`
  set N : Matrix T T ℤ := pmat ℤ π⁻¹ * Mmat E φ with hN
  set N' : Matrix T T ℤ := Mmat E φ.symm * pmat ℤ π with hN'
  have hNN' : N' * N = 1 := by
    rw [hN, hN', mul_assoc, ← mul_assoc (pmat ℤ π), pmat_mul_inv, one_mul, Mmat_symm_mul]
  have hcommZ : ∀ a, N * pmat ℤ (ρ a) = pmat ℤ (ρ a) * N := by
    intro a
    rw [hN, mul_assoc, Mmat_pmat, hπ a, ← mul_assoc, ← pmat_mul, ← mul_assoc (pmat ℤ (ρ a)),
      ← pmat_mul]
    congr 2
    group
  have hcomm : ∀ a, castQ N * pmat ℚ (ρ a) = pmat ℚ (ρ a) * castQ N := by
    intro a
    rw [← castQ_pmat, ← castQ_mul, ← castQ_mul, hcommZ]
  -- `M_{ι_a φ} = (ρ a π) N`
  have hM : ∀ a, castQ (Mmat E (φ.trans (MulAut.conj a))) = pmat ℚ (ρ a * π) * castQ N := by
    intro a
    rw [Mmat_conj, hN, ← castQ_pmat, ← castQ_mul, ← mul_assoc, ← pmat_mul, mul_assoc (ρ a),
      mul_inv_cancel, mul_one]
  have hW' : LatticeSignWitness N (fun a => pmat ℚ (ρ a * π)) := by
    rcases hW with ⟨U, hU, hWit⟩ | ⟨U₁, U₂, hU₁, hU₂, hWit⟩
    · exact Or.inl ⟨U, hU (castQ N) hcomm, hWit⟩
    · exact Or.inr ⟨U₁, U₂, hU₁ (castQ N) hcomm, hU₂ (castQ N) hcomm, hWit⟩
  have hinj : ∀ a : A, Injective (fun v => pmat ℚ (ρ a * π) *ᵥ v) := by
    intro a v w h
    have := congrArg (fun x => pmat ℚ (ρ a * π)⁻¹ *ᵥ x) h
    simpa only [mulVec_mulVec, pmat_inv_mul, one_mulVec] using this
  obtain ⟨a, v, hv, hfix⟩ := exists_fixed_of_lattice_sign_witness N N' hNN' _ hinj hW'
  rw [← reidemeisterAut_conj φ a]
  apply reidemeister_eq_top_of_fixed E _ v hv
  rw [hM a]
  exact hfix

end Main

/-! ### The induced automorphism of `ρ(A)` and the packaged criterion -/

section Packaged

variable {P : Subgroup A} [P.Characteristic] {ρ : A →* Equiv.Perm T} (E : PermModuleIso P ρ)

lemma pmat_injective {σ τ : Equiv.Perm T} (h : pmat ℤ σ = pmat ℤ τ) : σ = τ := by
  ext r
  have := congrArg (fun M => M *ᵥ Pi.single r (1 : ℤ)) h
  simp only [pmat_mulVec, pact_single_one] at this
  by_contra hne
  have := congrFun this (σ r)
  simp [Pi.single_apply, Ne.symm hne] at this

lemma rangeRestrict_eq_one_iff' (ρ : A →* Equiv.Perm T) (a : A) :
    ρ.rangeRestrict a = 1 ↔ ρ a = 1 := Subtype.ext_iff

include E in
/-- The kernel of `ρ` is invariant under every automorphism (a consequence of the equivariance
of `P^ab ≅ ℤ^T`, Corollary 2.5). -/
lemma rho_map_eq_one (φ : A ≃* A) {a : A} (ha : ρ a = 1) : ρ (φ a) = 1 := by
  have h := Mmat_pmat E φ a
  rw [ha, pmat_one, mul_one] at h
  have hinv : Mmat E φ * Mmat E φ.symm = 1 := by
    rw [← Mmat_trans, MulEquiv.symm_trans_self, Mmat_refl]
  have : pmat ℤ (ρ (φ a)) = pmat ℤ (1 : Equiv.Perm T) := by
    rw [pmat_one]
    calc pmat ℤ (ρ (φ a)) = pmat ℤ (ρ (φ a)) * Mmat E φ * Mmat E φ.symm := by
          rw [mul_assoc, hinv, mul_one]
      _ = 1 := by rw [← h, hinv]
  exact pmat_injective this

include E in
lemma ker_le_ker_comp (ψ : A ≃* A) :
    ρ.rangeRestrict.ker ≤ (ρ.rangeRestrict.comp ψ.toMonoidHom).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, rangeRestrict_eq_one_iff'] at hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, rangeRestrict_eq_one_iff']
  exact rho_map_eq_one E ψ hx

/-- The endomorphism `ρ a ↦ ρ (φ a)` of `ρ(A)`. -/
@[nolint unusedArguments]
noncomputable def inducedHom (φ : A ≃* A) : ρ.range →* ρ.range :=
  (ρ.rangeRestrict.liftOfSurjective ρ.rangeRestrict_surjective)
    ⟨ρ.rangeRestrict.comp φ.toMonoidHom, ker_le_ker_comp E φ⟩

lemma inducedHom_apply (φ : A ≃* A) (a : A) :
    inducedHom E φ (ρ.rangeRestrict a) = ρ.rangeRestrict (φ a) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a

lemma inducedHom_bijective (φ : A ≃* A) : Bijective (inducedHom E φ) := by
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨a, rfl⟩ := ρ.rangeRestrict_surjective x
    rw [inducedHom_apply, rangeRestrict_eq_one_iff'] at hx
    rw [rangeRestrict_eq_one_iff']
    have := rho_map_eq_one E φ.symm hx
    simpa using this
  · intro y
    obtain ⟨b, rfl⟩ := ρ.rangeRestrict_surjective y
    refine ⟨ρ.rangeRestrict (φ.symm b), ?_⟩
    rw [inducedHom_apply]; simp

/-- The automorphism `θ_φ` of the finite group `ρ(A)` induced by `φ ∈ Aut A`:
`θ_φ (ρ a) = ρ (φ a)` (§2 (definition of θ_α) / Corollary 2.5). -/
noncomputable def inducedAut (φ : A ≃* A) : ρ.range ≃* ρ.range :=
  MulEquiv.ofBijective (inducedHom E φ) (inducedHom_bijective E φ)

lemma inducedAut_apply (φ : A ≃* A) (a : A) :
    ((inducedAut E φ ⟨ρ a, a, rfl⟩ : ρ.range) : Equiv.Perm T) = ρ (φ a) := by
  have : (⟨ρ a, a, rfl⟩ : ρ.range) = ρ.rangeRestrict a := rfl
  rw [this, inducedAut, MulEquiv.ofBijective_apply, inducedHom_apply]
  rfl

/-- The hypothesis "`Out(ρ(A))` is generated by the class of conjugation by `π₀`": every
automorphism of the finite permutation group `ρ(A)` is conjugation by `g` or by `g π₀` for some
`g ∈ ρ(A)`.  (With `π₀ = 1` this says every automorphism is inner.) -/
def OutGeneratedBy (G : Subgroup (Equiv.Perm T)) (π₀ : Equiv.Perm T) : Prop :=
  ∀ θ : G ≃* G, ∃ g ∈ G, (∀ x : G, (θ x : Equiv.Perm T) = g * x * g⁻¹) ∨
    (∀ x : G, (θ x : Equiv.Perm T) = (g * π₀) * x * (g * π₀)⁻¹)

include E in
/-- **the Artin-group criterion (see lean/DIRECT_PROOF.md), packaged with the inner-coset reduction.**  Suppose every automorphism of `ρ(A)` is conjugation
by an element of `ρ(A)` or of `ρ(A) π₀`, and the witness condition holds for `π = 1` and for
`π = π₀`.  Then every automorphism of `A` has infinite Reidemeister number. -/
theorem rinf_of_outGeneratedBy [P.FiniteIndex] (π₀ : Equiv.Perm T)
    (hOut : OutGeneratedBy ρ.range π₀) (hInner : Witness ρ 1) (hOuter : Witness ρ π₀) :
    ∀ φ : A ≃* A, reidemeisterAut φ = ⊤ := by
  intro φ
  obtain ⟨g, ⟨b, rfl⟩, hg⟩ := hOut (inducedAut E φ)
  rcases hg with hg | hg
  · apply reidemeister_eq_top_of_witness E φ (ρ b * 1)
    · intro a
      rw [← inducedAut_apply E φ a, hg, mul_one]
    · exact hInner.mul_left b
  · apply reidemeister_eq_top_of_witness E φ (ρ b * π₀)
    · intro a
      rw [← inducedAut_apply E φ a, hg]
    · exact hOuter.mul_left b

include E in
/-- the inner-coset reduction: if every automorphism of `ρ(A)` is inner and the witness condition holds for
`π = 1`, then every automorphism of `A` has infinite Reidemeister number. -/
theorem rinf_of_allInner [P.FiniteIndex] (hOut : OutGeneratedBy ρ.range 1)
    (hInner : Witness ρ 1) : ∀ φ : A ≃* A, reidemeisterAut φ = ⊤ :=
  rinf_of_outGeneratedBy E 1 hOut hInner hInner

end Packaged

end ArtinRinf
