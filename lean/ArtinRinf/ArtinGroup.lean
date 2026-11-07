/-
# Artin groups of Coxeter matrices

`ArtinGroup M` is the presented group `⟨S | Π(s,t;m_st) = Π(t,s;m_st) (s ≠ t)⟩`, where
`Π(s,t;m) = s t s ⋯` has `m` letters.  The Coxeter group is Mathlib's `M.Group`
(the presented group with the extra relations `s² = 1`), and `toCoxeter : A → W` is the canonical
projection.  The pure Artin group is `P = ker (A → W)`.
-/
import Mathlib

open Function

namespace ArtinRinf

/-- The alternating product `Π(s,t;m) = s t s ⋯` with `m` factors. -/
def braidWord {G : Type*} [Monoid G] (s t : G) : ℕ → G
  | 0 => 1
  | n + 1 => s * braidWord t s n

@[simp] lemma braidWord_zero {G : Type*} [Monoid G] (s t : G) : braidWord s t 0 = 1 := rfl

lemma braidWord_succ {G : Type*} [Monoid G] (s t : G) (n : ℕ) :
    braidWord s t (n + 1) = s * braidWord t s n := rfl

lemma map_braidWord {G H : Type*} [Monoid G] [Monoid H] (f : G →* H) (s t : G) (n : ℕ) :
    f (braidWord s t n) = braidWord (f s) (f t) n := by
  induction n generalizing s t with
  | zero => simp
  | succ n ih => rw [braidWord_succ, map_mul, ih, braidWord_succ]

lemma braidWord_add_two {G : Type*} [Monoid G] (s t : G) (n : ℕ) :
    braidWord s t (n + 2) = s * t * braidWord s t n := by
  rw [braidWord_succ, braidWord_succ, mul_assoc]

lemma braidWord_even {G : Type*} [Monoid G] (s t : G) (k : ℕ) :
    braidWord s t (2 * k) = (s * t) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [show 2 * (k + 1) = 2 * k + 2 by ring, braidWord_add_two, ih, pow_succ']

lemma braidWord_odd {G : Type*} [Monoid G] (s t : G) (k : ℕ) :
    braidWord s t (2 * k + 1) = (s * t) ^ k * s := by
  induction k with
  | zero => simp [braidWord_succ]
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, braidWord_add_two, ih, pow_succ']
    simp only [mul_assoc]

/-- Coxeter relations imply braid relations. -/
lemma braid_of_coxeter {G : Type*} [Group G] (s t : G) (hs : s * s = 1) (ht : t * t = 1)
    (m : ℕ) (hm : (s * t) ^ m = 1) : braidWord s t m = braidWord t s m := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hts : t * s = (s * t)⁻¹ := by rw [mul_inv_rev, hs', ht']
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [braidWord_even, braidWord_even, hts, inv_pow]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add, ← two_mul]
    exact hm
  · rw [braidWord_odd, braidWord_odd, hts, inv_pow, eq_inv_mul_iff_mul_eq, ← mul_assoc]
    have h1 : (s * t) ^ k * (s * t) ^ k * (s * t) = 1 := by
      rw [← pow_add, ← pow_succ, show k + k + 1 = 2 * k + 1 by ring]; exact hm
    calc (s * t) ^ k * (s * t) ^ k * s = (s * t) ^ k * (s * t) ^ k * s * (t * t) := by
          rw [ht, mul_one]
      _ = ((s * t) ^ k * (s * t) ^ k * (s * t)) * t := by simp only [mul_assoc]
      _ = t := by rw [h1, one_mul]

variable {B : Type*} [DecidableEq B]

/-- The braid relator `Π(s,t;m) Π(t,s;m)⁻¹` in the free group. -/
def artinRel (M : CoxeterMatrix B) (i j : B) : FreeGroup B :=
  braidWord (FreeGroup.of i) (FreeGroup.of j) (M i j) *
    (braidWord (FreeGroup.of j) (FreeGroup.of i) (M i j))⁻¹

/-- The set of braid relators. -/
def artinRels (M : CoxeterMatrix B) : Set (FreeGroup B) :=
  {r | ∃ i j, i ≠ j ∧ r = artinRel M i j}

/-- The Artin group of the Coxeter matrix `M`. -/
def ArtinGroup (M : CoxeterMatrix B) : Type _ := PresentedGroup (artinRels M)

instance (M : CoxeterMatrix B) : Group (ArtinGroup M) :=
  inferInstanceAs (Group (PresentedGroup (artinRels M)))

namespace ArtinGroup

variable {M : CoxeterMatrix B}

/-- The standard generator `σ_i`. -/
def σ (M : CoxeterMatrix B) (i : B) : ArtinGroup M := PresentedGroup.of i

/-- The braid relations hold for the standard generators. -/
lemma braid (i j : B) : braidWord (σ M i) (σ M j) (M i j) = braidWord (σ M j) (σ M i) (M i j) := by
  by_cases hij : i = j
  · subst hij; rfl
  have h : (PresentedGroup.mk (artinRels M)) (artinRel M i j) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨i, j, hij, rfl⟩)
  rw [artinRel, map_mul, map_inv, mul_inv_eq_one, map_braidWord, map_braidWord] at h
  exact h

/-- The universal property: a family `f : B → G` satisfying the braid relations defines a
homomorphism `ArtinGroup M →* G`. -/
def lift {G : Type*} [Group G] (f : B → G)
    (hf : ∀ i j, i ≠ j → braidWord (f i) (f j) (M i j) = braidWord (f j) (f i) (M i j)) :
    ArtinGroup M →* G :=
  PresentedGroup.toGroup (rels := artinRels M) (f := f) (by
    rintro r ⟨i, j, hij, rfl⟩
    rw [artinRel, map_mul, map_inv, mul_inv_eq_one, map_braidWord, map_braidWord,
      FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    exact hf i j hij)

@[simp] lemma lift_σ {G : Type*} [Group G] (f : B → G)
    (hf : ∀ i j, i ≠ j → braidWord (f i) (f j) (M i j) = braidWord (f j) (f i) (M i j)) (i : B) :
    lift f hf (σ M i) = f i :=
  PresentedGroup.toGroup.of _

/-- Homomorphisms out of the Artin group agree if they agree on generators. -/
lemma hom_ext {G : Type*} [Group G] {φ ψ : ArtinGroup M →* G} (h : ∀ i, φ (σ M i) = ψ (σ M i)) :
    φ = ψ :=
  PresentedGroup.ext h

/-- The canonical projection `A → W` onto the Coxeter group. -/
def toCoxeter (M : CoxeterMatrix B) : ArtinGroup M →* M.Group :=
  lift (M.simple) (fun i j _ => by
    apply braid_of_coxeter
    · exact M.toCoxeterSystem.simple_mul_simple_self i
    · exact M.toCoxeterSystem.simple_mul_simple_self j
    · exact M.toCoxeterSystem.simple_mul_simple_pow i j)

@[simp] lemma toCoxeter_σ (i : B) : toCoxeter M (σ M i) = M.simple i := lift_σ _ _ i

lemma toCoxeter_surjective : Surjective (toCoxeter M) := by
  have : (toCoxeter M).range = ⊤ := by
    rw [eq_top_iff, ← M.toCoxeterSystem.subgroup_closure_range_simple, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨σ M i, toCoxeter_σ i⟩
  exact MonoidHom.range_eq_top.mp this

/-- The pure Artin group `P = ker (A → W)`. -/
def pure (M : CoxeterMatrix B) : Subgroup (ArtinGroup M) := (toCoxeter M).ker

lemma mem_pure {a : ArtinGroup M} : a ∈ pure M ↔ toCoxeter M a = 1 := Iff.rfl

instance pure_normal : (pure M).Normal := MonoidHom.normal_ker _

lemma sq_mem_pure (i : B) : σ M i ^ 2 ∈ pure M := by
  rw [pure, MonoidHom.mem_ker, map_pow, toCoxeter_σ, pow_two]
  exact M.toCoxeterSystem.simple_mul_simple_self i

/-- If the Coxeter group is finite, `P` has finite index. -/
lemma pure_finiteIndex [Finite M.Group] : (pure M).FiniteIndex := by
  constructor
  rw [pure, Subgroup.index_ker]
  exact Nat.card_pos.ne'

end ArtinGroup

end ArtinRinf
