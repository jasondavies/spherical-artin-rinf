/- A finite classification certificate for an infinite group's twisted classes. -/
import ArtinRinf.Reidemeister

namespace ArtinRinf

/-- A classification must establish invariance, completeness, and representatives
for every label. A finite orbit count alone is not sufficient. -/
structure TwistedClassification {G : Type*} [Group G] (φ : G →* G) (n : ℕ) where
  label : G → Fin n
  representative : Fin n → G
  invariant : ∀ x y, (twistedSetoid φ) x y → label x = label y
  complete : ∀ x, (twistedSetoid φ) x (representative (label x))
  label_representative : ∀ i, label (representative i) = i

noncomputable def TwistedClassification.equiv {G : Type*} [Group G]
    {φ : G →* G} {n : ℕ} (C : TwistedClassification φ n) : TwistedClasses φ ≃ Fin n where
  toFun := Quotient.lift C.label C.invariant
  invFun i := Quotient.mk'' (C.representative i)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn' with
    | h x => exact (Quotient.sound (C.complete x)).symm
  right_inv := C.label_representative

theorem TwistedClassification.reidemeister_eq {G : Type*} [Group G]
    {φ : G →* G} {n : ℕ} (C : TwistedClassification φ n) : reidemeister φ = n := by
  unfold reidemeister
  rw [ENat.card_congr C.equiv]
  simp

end ArtinRinf
