/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Twisted conjugacy and Reidemeister numbers

Paper, Lemma 2.1 (a)–(d).

For an endomorphism `φ : G →* G` two elements `x y : G` are `φ`-twisted conjugate if
`y = z * x * (φ z)⁻¹` for some `z`. The Reidemeister number `reidemeister φ : ℕ∞` is the number of
classes (`⊤` if there are infinitely many).
-/
import Mathlib

open Function

namespace ArtinRinf

variable {G : Type*} [Group G]

/-- The twisted conjugacy relation `x ~ y ↔ ∃ z, y = z * x * (φ z)⁻¹`. -/
def twistedSetoid (φ : G →* G) : Setoid G where
  r x y := ∃ z, y = z * x * (φ z)⁻¹
  iseqv := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨z, rfl⟩
      exact ⟨z⁻¹, by simp [mul_assoc]⟩
    · rintro x y w ⟨z, rfl⟩ ⟨z', rfl⟩
      exact ⟨z' * z, by simp [mul_assoc]⟩

/-- The set of `φ`-twisted conjugacy classes. -/
def TwistedClasses (φ : G →* G) : Type _ := Quotient (twistedSetoid φ)

/-- The Reidemeister number of an endomorphism, in `ℕ∞` (`⊤` = infinitely many classes). -/
noncomputable def reidemeister (φ : G →* G) : ℕ∞ := ENat.card (TwistedClasses φ)

/-- Reidemeister number of a group automorphism. -/
noncomputable abbrev reidemeisterAut (φ : G ≃* G) : ℕ∞ := reidemeister φ.toMonoidHom

lemma twisted_rel_iff (φ : G →* G) (x y : G) :
    (twistedSetoid φ) x y ↔ ∃ z, y = z * x * (φ z)⁻¹ := Iff.rfl

lemma reidemeister_eq_top_iff (φ : G →* G) : reidemeister φ = ⊤ ↔ Infinite (TwistedClasses φ) :=
  ENat.card_eq_top

/-! ### (a) Semiconjugacy / quotients -/

section Semiconj

variable {K : Type*} [Group K]

/-- If `p : G →* K` is surjective and `p ∘ φ = ψ ∘ p`, then `R(φ) ≥ R(ψ)`. -/
theorem reidemeister_le_of_surjective (φ : G →* G) (ψ : K →* K) (p : G →* K)
    (hp : Surjective p) (hcomm : ∀ x, p (φ x) = ψ (p x)) :
    reidemeister ψ ≤ reidemeister φ := by
  let F : TwistedClasses φ → TwistedClasses ψ :=
    Quotient.map' p (by
      rintro x y ⟨z, rfl⟩
      exact ⟨p z, by simp [hcomm]⟩)
  have hF : Surjective F := by
    intro c
    induction c using Quotient.inductionOn' with
    | h k =>
      obtain ⟨x, rfl⟩ := hp k
      exact ⟨Quotient.mk'' x, rfl⟩
  exact ENat.card_le_card_of_injective (injective_surjInv hF)

/-- An isomorphism intertwining `φ` and `ψ` preserves the Reidemeister number. -/
theorem reidemeister_eq_of_mulEquiv (φ : G →* G) (ψ : K →* K) (e : G ≃* K)
    (hcomm : ∀ x, e (φ x) = ψ (e x)) : reidemeister φ = reidemeister ψ := by
  refine le_antisymm ?_ (reidemeister_le_of_surjective φ ψ e.toMonoidHom e.surjective hcomm)
  refine reidemeister_le_of_surjective ψ φ e.symm.toMonoidHom e.symm.surjective ?_
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  apply e.injective
  simp [hcomm]

/-- Lemma 2.1(a): for a normal subgroup `N` with `φ(N) ≤ N`, `R(φ) ≥ R(φ̄)` on `G ⧸ N`. -/
theorem reidemeister_quotient_le (φ : G →* G) (N : Subgroup G) [N.Normal]
    (hN : N ≤ N.comap φ) :
    reidemeister (QuotientGroup.map N N φ hN) ≤ reidemeister φ :=
  reidemeister_le_of_surjective φ _ (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (fun _ => rfl)

/-- Lemma 2.1(a) for the abelianisation: `R(φ) ≥ R(φ^ab)`. -/
theorem reidemeister_abelianization_le (φ : G →* G) :
    reidemeister (Abelianization.map φ) ≤ reidemeister φ :=
  reidemeister_le_of_surjective φ _ Abelianization.of
    (QuotientGroup.mk'_surjective _) (fun _ => rfl)

end Semiconj

/-! ### (b) Twisting by inner automorphisms -/

/-- Lemma 2.1(c): `R(ι_g ∘ φ) = R(φ)`, where `ι_g x = g x g⁻¹`. -/
theorem reidemeister_inner_comp (φ : G →* G) (g : G) :
    reidemeister ((MulAut.conj g).toMonoidHom.comp φ) = reidemeister φ := by
  unfold reidemeister
  apply ENat.card_congr
  -- right multiplication by `g` is a bijection between the class sets
  refine
    { toFun := Quotient.map' (fun x => x * g) ?_
      invFun := Quotient.map' (fun x => x * g⁻¹) ?_
      left_inv := ?_
      right_inv := ?_ }
  · rintro x y ⟨z, rfl⟩
    exact ⟨z, by simp [mul_assoc]⟩
  · rintro x y ⟨z, rfl⟩
    exact ⟨z, by simp [mul_assoc]⟩
  · intro c
    induction c using Quotient.inductionOn' with
    | h a => exact congrArg Quotient.mk'' (by simp)
  · intro c
    induction c using Quotient.inductionOn' with
    | h a => exact congrArg Quotient.mk'' (by simp)

/-! ### (c) Finite-index subgroups -/

section Restrict

/-- The restriction of `φ` to an invariant subgroup. -/
def restrictEnd (φ : G →* G) (H : Subgroup G) (hH : ∀ x ∈ H, φ x ∈ H) : H →* H :=
  (φ.comp H.subtype).codRestrict H (fun x => hH x x.2)

@[simp] lemma restrictEnd_coe (φ : G →* G) (H : Subgroup G) (hH : ∀ x ∈ H, φ x ∈ H) (x : H) :
    ((restrictEnd φ H hH x : H) : G) = φ x := rfl

/-- Lemma 2.1(d): `R(φ|_H) ≤ [G:H] · R(φ)` for a `φ`-invariant subgroup of finite index. -/
theorem reidemeister_restrict_le (φ : G →* G) (H : Subgroup G) [H.FiniteIndex]
    (hH : ∀ x ∈ H, φ x ∈ H) :
    reidemeister (restrictEnd φ H hH) ≤ (H.index : ℕ∞) * reidemeister φ := by
  classical
  set ψ := restrictEnd φ H hH
  -- the natural map from `ψ`-classes to `φ`-classes
  let ι : TwistedClasses ψ → TwistedClasses φ :=
    Quotient.map' (fun x : H => (x : G)) (by
      rintro x y ⟨z, rfl⟩
      exact ⟨z, by simp [ψ]⟩)
  have hι : ∀ c : TwistedClasses ψ, ι c = Quotient.mk'' ((Quotient.out c : H) : G) := by
    intro c
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  -- `out c` is `φ`-conjugate to the chosen representative of `ι c`
  have hz : ∀ c : TwistedClasses ψ, ∃ z : G,
      ((Quotient.out c : H) : G) = z * Quotient.out (ι c) * (φ z)⁻¹ := by
    intro c
    have h1 : (Quotient.mk'' (Quotient.out (ι c)) : TwistedClasses φ)
        = Quotient.mk'' ((Quotient.out c : H) : G) := by
      rw [← hι c]; exact Quotient.out_eq _
    exact Quotient.exact h1
  let z : TwistedClasses ψ → G := fun c => Classical.choose (hz c)
  have hzspec : ∀ c, ((Quotient.out c : H) : G) = z c * Quotient.out (ι c) * (φ (z c))⁻¹ :=
    fun c => Classical.choose_spec (hz c)
  let F : TwistedClasses ψ → TwistedClasses φ × (G ⧸ H) :=
    fun c => (ι c, (QuotientGroup.mk (z c)⁻¹ : G ⧸ H))
  have hF : Injective F := by
    intro c c' hcc
    simp only [F, Prod.mk.injEq] at hcc
    obtain ⟨h1, h2⟩ := hcc
    rw [QuotientGroup.eq] at h2
    simp only [inv_inv] at h2
    -- `h := z c * (z c')⁻¹ ∈ H` conjugates `out c'` to `out c`
    set h : H := ⟨z c * (z c')⁻¹, h2⟩
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    apply Quotient.sound
    refine ⟨h⁻¹, ?_⟩
    apply Subtype.ext
    have e1 := hzspec c
    have e2 := hzspec c'
    rw [h1] at e1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, restrictEnd_coe, ψ, map_inv, h]
    rw [e1, e2]
    simp [mul_assoc]
  calc reidemeister ψ ≤ ENat.card (TwistedClasses φ × (G ⧸ H)) :=
        ENat.card_le_card_of_injective hF
    _ = reidemeister φ * (H.index : ℕ∞) := by
        rw [ENat.card_prod, reidemeister, Subgroup.index_eq_card, ENat.card_eq_coe_natCard (G ⧸ H)]
    _ = (H.index : ℕ∞) * reidemeister φ := mul_comm _ _

/-- Lemma 2.1(d), consequence: if `R(φ|_H) = ∞` for an invariant finite-index subgroup `H`,
then `R(φ) = ∞`. -/
theorem reidemeister_eq_top_of_restrict (φ : G →* G) (H : Subgroup G) [H.FiniteIndex]
    (hH : ∀ x ∈ H, φ x ∈ H) (h : reidemeister (restrictEnd φ H hH) = ⊤) :
    reidemeister φ = ⊤ := by
  have := reidemeister_restrict_le φ H hH
  rw [h, top_le_iff] at this
  by_contra hne
  have hfin : (H.index : ℕ∞) ≠ ⊤ := ENat.natCast_ne_top _
  exact WithTop.mul_ne_top hfin hne this

end Restrict

end ArtinRinf
