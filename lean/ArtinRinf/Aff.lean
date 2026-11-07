/-
# The semidirect product `R^T ⋊ Perm T`

Elements are pairs `(v, σ)` with `(v, σ)(w, τ) = (v + σ·w, στ)`, where `σ·w = pact σ w`.
We use a hand-rolled structure (rather than `SemidirectProduct`) so that equality is decidable and
small identities can be checked by `decide`.
-/
import ArtinRinf.PermMatrix

namespace ArtinRinf

/-- `R^T ⋊ Perm T`. -/
@[ext] structure Aff (R T : Type*) where
  /-- translation part -/
  v : T → R
  /-- permutation part -/
  σ : Equiv.Perm T

namespace Aff

variable {R T : Type*} [CommRing R]

lemma pact_add (σ : Equiv.Perm T) (x y : T → R) : pact σ (x + y) = pact σ x + pact σ y := rfl
lemma pact_neg (σ : Equiv.Perm T) (x : T → R) : pact σ (-x) = -pact σ x := rfl
lemma pact_zero (σ : Equiv.Perm T) : pact σ (0 : T → R) = 0 := rfl

lemma pact_mul' (σ τ : Equiv.Perm T) (v : T → R) :
    pact (σ * τ) v = pact σ (pact τ v) := by
  ext i; simp [pact, Equiv.Perm.mul_def]

instance : Mul (Aff R T) := ⟨fun a b => ⟨a.v + pact a.σ b.v, a.σ * b.σ⟩⟩
instance : One (Aff R T) := ⟨⟨0, 1⟩⟩
instance : Inv (Aff R T) := ⟨fun a => ⟨-pact a.σ⁻¹ a.v, a.σ⁻¹⟩⟩

@[simp] lemma mul_v (a b : Aff R T) : (a * b).v = a.v + pact a.σ b.v := rfl
@[simp] lemma mul_σ (a b : Aff R T) : (a * b).σ = a.σ * b.σ := rfl
@[simp] lemma one_v : (1 : Aff R T).v = 0 := rfl
@[simp] lemma one_σ : (1 : Aff R T).σ = 1 := rfl
@[simp] lemma inv_v (a : Aff R T) : a⁻¹.v = -pact a.σ⁻¹ a.v := rfl
@[simp] lemma inv_σ (a : Aff R T) : a⁻¹.σ = a.σ⁻¹ := rfl

instance : Group (Aff R T) where
  mul_assoc a b c := by
    ext1
    · simp [pact_add, pact_mul', add_assoc]
    · simp [mul_assoc]
  one_mul a := by ext1 <;> simp
  mul_one a := by ext1 <;> simp [pact_zero]
  inv_mul_cancel a := by
    ext1
    · simp only [mul_v, inv_v, inv_σ, one_v]
      rw [neg_add_eq_zero]
    · simp
  npow := npowRec
  zpow := zpowRec

instance [Fintype T] [DecidableEq T] [DecidableEq R] : DecidableEq (Aff R T) := fun a b =>
  decidable_of_iff (a.v = b.v ∧ a.σ = b.σ) (by
    constructor
    · rintro ⟨h1, h2⟩; exact Aff.ext h1 h2
    · rintro rfl; exact ⟨rfl, rfl⟩)

/-- The permutation part, as a homomorphism. -/
def toPerm : Aff R T →* Equiv.Perm T where
  toFun a := a.σ
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma toPerm_apply (a : Aff R T) : toPerm a = a.σ := rfl

/-- Reduction of coefficients along a ring homomorphism. -/
def mapRing {S : Type*} [CommRing S] (f : R →+* S) : Aff R T →* Aff S T where
  toFun a := ⟨fun i => f (a.v i), a.σ⟩
  map_one' := by ext1 <;> (try funext i) <;> simp
  map_mul' a b := by ext1 <;> (try funext i) <;> simp [pact]

@[simp] lemma mapRing_v {S : Type*} [CommRing S] (f : R →+* S) (a : Aff R T) (i : T) :
    (mapRing f a).v i = f (a.v i) := rfl
@[simp] lemma mapRing_σ {S : Type*} [CommRing S] (f : R →+* S) (a : Aff R T) :
    (mapRing f a).σ = a.σ := rfl

/-- Elements with trivial permutation part multiply by adding translation parts. -/
lemma mul_v_of_σ_eq_one (a b : Aff R T) (ha : a.σ = 1) : (a * b).v = a.v + b.v := by
  simp [ha]

/-- Conjugating a pure translation. -/
lemma conj_v (a b : Aff R T) (hb : b.σ = 1) : (a * b * a⁻¹).v = pact a.σ b.v := by
  simp only [mul_v, mul_σ, hb, mul_one, inv_v, pact_add, pact_neg]
  rw [← pact_mul', mul_inv_cancel, pact_one]
  abel

lemma conj_σ (a b : Aff R T) (hb : b.σ = 1) : (a * b * a⁻¹).σ = 1 := by
  simp [hb]

end Aff

end ArtinRinf
