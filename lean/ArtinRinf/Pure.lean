/-
# The abelianised pure Artin group as a permutation module (paper, Lemma 2.4 and Proposition 2.6)

Given explicit data — the permutations `gens i` of a finite set `T` (the reflections), induced by
the simple reflections, and the positions `sidx i ∈ T` of the simple reflections — satisfying
finitely many decidable conditions, we construct

* the homomorphism `f : A → ℤ^T ⋊ Perm T`, `σ_i ↦ (e_{s_i}, ρ(s_i))` (Lemma 2.4);
* `ρ : A → Perm T`, its permutation part;
* an equivariant surjection `P^ab → ℤ^T`, `[p] ↦ f(p)/2` (Proposition 2.6, surjectivity and
  equivariance);

and, **assuming** that `P^ab` is free abelian of rank `|T|` (Brieskorn; Orlik–Terao), we conclude
that this surjection is an isomorphism (finitely generated free abelian groups are Hopfian).
-/
import ArtinRinf.ArtinGroup
import ArtinRinf.Aff
import ArtinRinf.Criterion

open Function

namespace ArtinRinf

variable {B : Type*} [DecidableEq B] {T : Type*} [Fintype T] [DecidableEq T]

/-- The image of the `i`-th generator in `R^T ⋊ Perm T`. -/
def affGen (R : Type*) [CommRing R] (gens : B → Equiv.Perm T) (sidx : B → T) (i : B) : Aff R T :=
  ⟨Pi.single (sidx i) 1, gens i⟩

/-- Explicit data describing the conjugation action of `W(M)` on its reflections, together with
the finite certificates needed for Lemma 2.4 and Proposition 2.6. All fields are decidable for
concrete data. -/
structure ReflData (M : CoxeterMatrix B) (T : Type*) [Fintype T] [DecidableEq T] where
  /-- the permutation of the reflections induced by conjugation with `s_i` -/
  gens : B → Equiv.Perm T
  /-- the reflection `s_i` as a point of `T` -/
  sidx : B → T
  gens_sq : ∀ i, gens i * gens i = 1
  gens_fix : ∀ i, gens i (sidx i) = sidx i
  /-- Lemma 2.4: the braid relations hold in `ℤ^T ⋊ Perm T` -/
  braid : ∀ i j, i ≠ j → braidWord (affGen ℤ gens sidx i) (affGen ℤ gens sidx j) (M i j) =
    braidWord (affGen ℤ gens sidx j) (affGen ℤ gens sidx i) (M i j)
  /-- the Coxeter relations hold in `(ℤ/2)^T ⋊ Perm T` (used to show `f(P) ⊆ 2ℤ^T`) -/
  cox2 : ∀ i j, (affGen (ZMod 2) gens sidx i * affGen (ZMod 2) gens sidx j) ^ (M i j) = 1
  /-- every reflection is conjugate to a simple one: `t = w s_i w⁻¹`, `w` a word -/
  orbWord : T → List B × B
  orb : ∀ t, ((orbWord t).1.map gens).prod (sidx (orbWord t).2) = t

namespace ReflData

variable {M : CoxeterMatrix B} (D : ReflData M T)

open ArtinGroup

/-- The homomorphism `f : A → ℤ^T ⋊ Perm T` of Lemma 2.4. -/
def f : ArtinGroup M →* Aff ℤ T := ArtinGroup.lift (affGen ℤ D.gens D.sidx) D.braid

/-- The permutation representation `ρ : A → Perm T` (conjugation action of `W` on reflections). -/
def ρ : ArtinGroup M →* Equiv.Perm T := Aff.toPerm.comp D.f

@[simp] lemma f_σ (i : B) : D.f (σ M i) = affGen ℤ D.gens D.sidx i := lift_σ _ _ i

@[simp] lemma ρ_σ (i : B) : D.ρ (σ M i) = D.gens i := by
  simp [ρ, affGen]

lemma ρ_list_prod (w : List B) : D.ρ (w.map (σ M)).prod = (w.map D.gens).prod := by
  rw [map_list_prod, List.map_map]
  congr 1

lemma f_σ_v (a : ArtinGroup M) : (D.f a).σ = D.ρ a := rfl

/-- The mod-2 reduction of `f` factors through the Coxeter group. -/
def f2W : M.Group →* Aff (ZMod 2) T :=
  M.toCoxeterSystem.lift ⟨affGen (ZMod 2) D.gens D.sidx, D.cox2⟩

lemma mapRing_affGen (i : B) :
    Aff.mapRing (Int.castRingHom (ZMod 2)) (affGen ℤ D.gens D.sidx i) =
      affGen (ZMod 2) D.gens D.sidx i := by
  ext1
  · funext t
    simp only [Aff.mapRing_v, affGen, Pi.single_apply]
    split_ifs <;> simp
  · rfl

lemma mod2_factor :
    (Aff.mapRing (Int.castRingHom (ZMod 2))).comp D.f = D.f2W.comp (toCoxeter M) := by
  apply hom_ext
  intro i
  simp only [MonoidHom.comp_apply, f_σ, toCoxeter_σ, mapRing_affGen, f2W]
  rw [← M.toCoxeterSystem.lift_apply_simple D.cox2 i]
  rfl

lemma f_pure (p : ArtinGroup M) (hp : p ∈ pure M) :
    (D.f p).σ = 1 ∧ ∀ t, (2 : ℤ) ∣ (D.f p).v t := by
  have h := congrArg (fun φ => φ p) D.mod2_factor
  simp only [MonoidHom.comp_apply] at h
  rw [mem_pure] at hp
  rw [hp, map_one] at h
  refine ⟨by simpa using congrArg Aff.σ h, fun t => ?_⟩
  have := congrFun (congrArg Aff.v h) t
  simp only [Aff.mapRing_v, Aff.one_v, Pi.zero_apply, eq_intCast] at this
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp this

lemma ρ_pure (p : ArtinGroup M) (hp : p ∈ pure M) : D.ρ p = 1 := (D.f_pure p hp).1

/-- `p ↦ f(p)/2`, a homomorphism `P → ℤ^T`. -/
def half : pure M →* Multiplicative (T → ℤ) where
  toFun p := Multiplicative.ofAdd (fun t => (D.f p).v t / 2)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext t
    simp
  map_mul' p q := by
    apply Multiplicative.toAdd.injective
    funext t
    simp only [Subgroup.coe_mul, map_mul, toAdd_ofAdd, toAdd_mul, Pi.add_apply]
    rw [Aff.mul_v_of_σ_eq_one _ _ (D.f_pure p p.2).1, Pi.add_apply,
      Int.add_ediv_of_dvd_left ((D.f_pure p p.2).2 t)]

/-- The induced homomorphism `P^ab → ℤ^T`. -/
def ebar : Abelianization (pure M) →* Multiplicative (T → ℤ) := Abelianization.lift D.half

lemma ebar_of (p : pure M) :
    (D.ebar (Abelianization.of p)).toAdd = fun t => (D.f p).v t / 2 := by
  simp [ebar, half]

/-- Equivariance (Proposition 2.6). -/
lemma ebar_equivariant (a : ArtinGroup M) (p : pure M) :
    (D.ebar (Abelianization.of (conjP (pure M) a p))).toAdd =
      pact (D.ρ a) (D.ebar (Abelianization.of p)).toAdd := by
  rw [ebar_of, ebar_of]
  funext t
  simp only [conjP_coe, map_mul, map_inv, pact_apply]
  rw [Aff.conj_v _ _ (D.f_pure p p.2).1]
  rfl

/-- Surjectivity (Proposition 2.6): `f(P) = 2ℤ^T`. -/
lemma ebar_surjective : Surjective D.ebar := by
  -- the basis vectors are in the range
  have hbasis : ∀ t, Multiplicative.ofAdd (Pi.single t (1 : ℤ)) ∈ D.ebar.range := by
    intro t
    set w := (D.orbWord t).1
    set i := (D.orbWord t).2
    set a : ArtinGroup M := (w.map (σ M)).prod
    refine ⟨Abelianization.of (conjP (pure M) a ⟨σ M i ^ 2, sq_mem_pure i⟩), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [ebar_equivariant, ebar_of]
    have hf2 : (D.f (σ M i ^ 2)).v = fun s => 2 * (Pi.single (D.sidx i) (1 : ℤ) : T → ℤ) s := by
      rw [pow_two, map_mul, f_σ, Aff.mul_v]
      funext s
      simp only [affGen, Pi.add_apply]
      rw [pact_single_one, D.gens_fix]
      ring
    simp only [hf2]
    funext s
    simp only [pact_apply, Int.mul_ediv_cancel_left _ two_ne_zero, toAdd_ofAdd]
    have ht : D.ρ a (D.sidx i) = t := by
      rw [ρ_list_prod]; exact D.orb t
    simp only [Pi.single_apply]
    congr 1
    apply propext
    constructor
    · intro h; rw [← ht, ← h]; simp
    · intro h; rw [h, ← ht]; simp
  -- hence everything is
  intro x
  have hx : x = ∏ t, Multiplicative.ofAdd (x.toAdd t • Pi.single t (1 : ℤ)) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    simp only [toAdd_ofAdd]
    conv_lhs => rw [← Finset.univ_sum_single x.toAdd]
    congr 1; funext t
    funext s
    by_cases h : s = t
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [hx]
  show _ ∈ D.ebar.range
  refine Subgroup.prod_mem _ (fun t _ => ?_)
  have : Multiplicative.ofAdd (x.toAdd t • (Pi.single t (1 : ℤ) : T → ℤ)) =
      (Multiplicative.ofAdd (Pi.single t (1 : ℤ) : T → ℤ)) ^ (x.toAdd t) := by
    rw [← ofAdd_zsmul]
  rw [this]
  exact Subgroup.zpow_mem _ (hbasis t) _

/-- **Proposition 2.6** (modulo the cited rank statement): if `P^ab ≅ ℤ^T` abstractly
(Brieskorn: `P = π₁` of the complement of the reflection arrangement; its `H₁` is free abelian on
the meridians, one per reflection), then `[p] ↦ f(p)/2` is an `A`-equivariant isomorphism
`P^ab ≅ ℤ^T`. -/
noncomputable def permModuleIso (hBr : Nonempty (Abelianization (pure M) ≃* Multiplicative (T → ℤ))) :
    PermModuleIso (pure M) D.ρ := by
  classical
  let β := hBr.some
  -- the endomorphism `ebar ∘ β⁻¹` of `ℤ^T`, as a `ℤ`-linear map
  let L : (T → ℤ) →+ (T → ℤ) :=
    { toFun := fun x => (D.ebar (β.symm (Multiplicative.ofAdd x))).toAdd
      map_zero' := by simp
      map_add' := fun x y => by simp }
  have hLs : Surjective L.toIntLinearMap := by
    intro y
    obtain ⟨z, hz⟩ := D.ebar_surjective (Multiplicative.ofAdd y)
    exact ⟨(β z).toAdd, by simp [L, hz]⟩
  have hLi := OrzechProperty.injective_of_surjective_endomorphism L.toIntLinearMap hLs
  have hinj : Injective D.ebar := by
    intro x y hxy
    have : L.toIntLinearMap (β x).toAdd = L.toIntLinearMap (β y).toAdd := by
      simp [L, hxy]
    have := hLi this
    exact β.injective (Multiplicative.toAdd.injective this)
  exact ⟨MulEquiv.ofBijective D.ebar ⟨hinj, D.ebar_surjective⟩, fun a p => D.ebar_equivariant a p⟩

/-- **Main theorem for a type given by explicit data** (Theorem 3.1 + Remark 3.2 +
Proposition 2.6).  The hypotheses `hW`, `hCP`, `hBr` stand for cited theorems; `hOut` for the
computation of `Out(W/Z(W))`; `hInner`, `hOuter` are the finite certificates. -/
theorem rinf (hW : Finite M.Group) (hCP : (pure M).Characteristic)
    (hBr : Nonempty (Abelianization (pure M) ≃* Multiplicative (T → ℤ)))
    (π₀ : Equiv.Perm T) (hOut : OutGeneratedBy D.ρ.range π₀)
    (hInner : Witness D.ρ 1) (hOuter : Witness D.ρ π₀) :
    ∀ φ : ArtinGroup M ≃* ArtinGroup M, reidemeisterAut φ = ⊤ := by
  have := hW
  have := hCP
  haveI : (pure M).FiniteIndex := pure_finiteIndex (M := M)
  exact rinf_of_outGeneratedBy (D.permModuleIso hBr) π₀ hOut hInner hOuter

end ReflData

end ArtinRinf
