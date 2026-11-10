/- Identify the presented Artin quotient with the concrete affine extension. -/
import ArtinRinf.Dihedral5.Presentation

namespace ArtinRinf.Dihedral5
namespace Presentation

open ArtinGroup

lemma hol_coxeter : ∀ i j : Fin 2, (holGen i * holGen j) ^ (M i j) = 1 := by
  decide +kernel

def coxHol : M.Group →* Hol := M.toCoxeterSystem.lift ⟨holGen, hol_coxeter⟩

lemma toHol_factor : toHol = coxHol.comp (toCoxeter M) := by
  apply ArtinGroup.hom_ext
  intro i
  simp only [MonoidHom.comp_apply, toCoxeter_σ, toHol_gen, coxHol]
  rw [← M.toCoxeterSystem.lift_apply_simple hol_coxeter i]
  simp only [CoxeterMatrix.toCoxeterSystem_simple]

def conjugator : I → A := ![1, 1, gen 1, gen 0 * gen 1, gen 0]
def simpleIndex : I → Fin 2 := ![0, 1, 0, 0, 1]

lemma meridian_form (i : I) : (meridian i).val =
    conjugator i * (gen (simpleIndex i))^2 * (conjugator i)⁻¹ := by
  fin_cases i <;> norm_num [meridian, conjugator, simpleIndex] <;> rw [edge_val]
  all_goals norm_num [eval, words, next_table]
  all_goals group
  all_goals simp only [zpow_two, mul_assoc]

lemma meridian_coxeter (i : I) : toCoxeter M (meridian i).val = 1 := by
  rw [meridian_form, map_mul, map_mul, map_inv,
    show toCoxeter M ((gen (simpleIndex i))^2) = 1 from sq_mem_pure (simpleIndex i)]
  simp

/-- The ten-coset kernel is the actual pure Artin subgroup. -/
theorem kernel_eq_pure : P = pure M := by
  have hle : Subgroup.closure (Set.range meridian) ≤ ((toCoxeter M).comp P.subtype).ker := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact meridian_coxeter i
  rw [meridians_generate] at hle
  apply le_antisymm
  · intro x hx
    exact hle (show (⟨x, hx⟩ : P) ∈ (⊤ : Subgroup P) from trivial)
  · intro x hx
    change toHol x = 1
    rw [toHol_factor, MonoidHom.comp_apply, show toCoxeter M x = 1 from hx, map_one]

lemma translation_injective : Function.Injective translation := by
  intro x y h
  simpa [translation] using congrArg coordinates h

def halfCoords (p : P) : V := coordinates (toGamma p.val)

lemma image_translation (p : P) : toGamma p.val = translation (halfCoords p) := by
  have h := element_coordinates (toGamma p.val)
  have hg : (toGamma p.val).val.g = 1 := p.property
  rw [hg] at h
  exact h.symm

def half : P →* Multiplicative V where
  toFun p := Multiplicative.ofAdd (halfCoords p)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change coordinates (toGamma 1) = 0
    rw [map_one]
    decide +kernel
  map_mul' p q := by
    apply Multiplicative.toAdd.injective
    apply translation_injective
    change translation (halfCoords (p * q)) = translation (halfCoords p + halfCoords q)
    rw [translation_add, ← image_translation, ← image_translation, ← image_translation]
    exact toGamma.map_mul p.val q.val

def affineEdge (j : Fin 10) (i : Fin 2) : Gamma :=
  ((words j).map affineGen).prod * affineGen i * (((words (next j i)).map affineGen).prod)⁻¹

lemma toGamma_edge (j : Fin 10) (i : Fin 2) : toGamma (edge j i).val = affineEdge j i := by
  simp only [edge_val, map_mul, map_inv, eval, map_list_prod, List.map_map,
    Function.comp_def, toGamma_gen, affineEdge]

lemma meridian_image : ∀ i : I, toGamma (meridian i).val = translation (Pi.single i 1) := by
  intro i
  fin_cases i <;> norm_num [meridian] <;> rw [toGamma_edge]
  all_goals apply Subtype.ext; apply Ambient.ext <;> decide +kernel

lemma half_meridian (i : I) : half (meridian i) = Multiplicative.ofAdd (Pi.single i 1) := by
  apply Multiplicative.toAdd.injective
  apply translation_injective
  change translation (halfCoords (meridian i)) = translation (Pi.single i 1)
  rw [← image_translation, meridian_image]

def abelianHalf : Abelianization P →* Multiplicative V := Abelianization.lift half

def fromLattice : Multiplicative V →* Abelianization P where
  toFun x := ∏ i : I, (Abelianization.of (meridian i)) ^ (x.toAdd i)
  map_one' := by simp
  map_mul' x y := by simp [zpow_add, Finset.prod_mul_distrib]

lemma fromLattice_basis (i : I) :
    fromLattice (Multiplicative.ofAdd (Pi.single i 1)) = Abelianization.of (meridian i) := by
  simp [fromLattice, Pi.single_apply]

lemma abelianHalf_fromLattice (x : Multiplicative V) : abelianHalf (fromLattice x) = x := by
  apply Multiplicative.toAdd.injective
  simp only [fromLattice, MonoidHom.coe_mk, OneHom.coe_mk, map_prod, map_zpow,
    abelianHalf, Abelianization.lift_apply_of, half_meridian, toAdd_prod,
    toAdd_zpow, toAdd_ofAdd]
  ext i
  simp [Pi.single_apply]

lemma fromLattice_surjective : Function.Surjective fromLattice := by
  intro x
  change x ∈ fromLattice.range
  induction x using QuotientGroup.induction_on with
  | H p =>
    have hp : p ∈ Subgroup.closure (Set.range meridian) := by rw [meridians_generate]; trivial
    change Abelianization.of p ∈ fromLattice.range
    induction hp using Subgroup.closure_induction with
    | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      exact ⟨Multiplicative.ofAdd (Pi.single i 1), fromLattice_basis i⟩
    | one => simp
    | mul p q _ _ hp hq => simpa only [map_mul] using fromLattice.range.mul_mem hp hq
    | inv p _ hp => simpa only [map_inv] using fromLattice.range.inv_mem hp

/-- The rank-five pure abelianisation is proved here, not assumed from arrangement theory. -/
theorem abelianHalf_bijective : Function.Bijective abelianHalf := by
  constructor
  · intro x y h
    obtain ⟨u, rfl⟩ := fromLattice_surjective x
    obtain ⟨v, rfl⟩ := fromLattice_surjective y
    rw [abelianHalf_fromLattice, abelianHalf_fromLattice] at h
    rw [h]
  · intro x
    exact ⟨fromLattice x, abelianHalf_fromLattice x⟩

lemma pure_kernel (p : P) : toGamma p.val = 1 ↔ Abelianization.of p = 1 := by
  constructor
  · intro h
    apply abelianHalf_bijective.1
    rw [map_one]
    change half p = 1
    apply Multiplicative.toAdd.injective
    change coordinates (toGamma p.val) = 0
    rw [h]
    decide +kernel
  · intro h
    have hh := congrArg abelianHalf h
    rw [map_one] at hh
    change half p = 1 at hh
    have hc : halfCoords p = 0 := congrArg Multiplicative.toAdd hh
    rw [image_translation, hc, translation_zero]

/-- The affine map has exactly the commutator of the actual pure Artin group as kernel. -/
theorem toGamma_kernel : toGamma.ker = ⁅pure M, pure M⁆ := by
  rw [← kernel_eq_pure, ← P.map_subtype_commutator]
  ext x
  constructor
  · intro hx
    have hp : x ∈ P := by
      change holonomy (toGamma x) = 1
      rw [show toGamma x = 1 from hx, map_one]
    refine ⟨⟨x, hp⟩, ?_, rfl⟩
    rw [← Abelianization.ker_of]
    exact (pure_kernel ⟨x, hp⟩).mp hx
  · rintro ⟨p, hp, rfl⟩
    apply (pure_kernel p).mpr
    rw [← Abelianization.ker_of] at hp
    exact hp

/-- The crystallographic quotient of the presented Artin group I₂(5). -/
abbrev ArtinQuotient := A ⧸ ⁅pure M, pure M⁆

/-- No arrangement-homology or group-identification hypothesis is required. -/
noncomputable def quotientEquiv : ArtinQuotient ≃* Gamma :=
  (QuotientGroup.quotientMulEquivOfEq toGamma_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective toGamma toGamma_surjective)

/-- Proposition C for the actual presented Artin quotient. -/
theorem artinQuotient_exists_reidemeister_eighteen :
    ∃ ψ : ArtinQuotient ≃* ArtinQuotient, reidemeisterAut ψ = 18 :=
  exists_reidemeister_eighteen quotientEquiv

theorem artinQuotient_not_R_infty :
    ¬ ∀ ψ : ArtinQuotient ≃* ArtinQuotient, reidemeisterAut ψ = ⊤ := by
  intro h
  obtain ⟨ψ, hψ⟩ := artinQuotient_exists_reidemeister_eighteen
  have hbad : (18 : ℕ∞) = ⊤ := hψ.symm.trans (h ψ)
  norm_num at hbad

end Presentation
end ArtinRinf.Dihedral5
