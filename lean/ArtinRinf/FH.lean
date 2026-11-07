/-
# The Franzsen–Howlett reduction (alternative Artin-group proof)

* `FranzsenHowlett M`: every automorphism of the Coxeter group `W = M.Group` is a reflection-preserving
  automorphism composed with a central twist ([FH03, Thm. 31]).  This is a statement about Mathlib's
  Coxeter group alone.
* From it (and Cohen–Paris) we derive: for every `φ ∈ Aut(A)`, the image `ρ(φ(σ_i))` of each standard
  generator is a reflection permutation `rp(x_i)`.
* A *search-tree certificate* (`TreeCert`, an orbit/stabiliser reduction checked by the kernel) then shows
  that every tuple of reflections with the Coxeter orders of the generators is conjugate to the tuple of
  simple reflections by an element of `ρ(W)` or `ρ(W)π₀`.  Hence the induced automorphism of `ρ(W)` is
  conjugation by an element of `ρ(W)⟨π₀⟩`, and the Artin-group criterion (see lean/DIRECT_PROOF.md) applies.
-/
import ArtinRinf.OutCert

open Function

namespace ArtinRinf

/-! ### The Franzsen–Howlett property of a Coxeter group -/

section FHdef

variable {B : Type*} [DecidableEq B] (M : CoxeterMatrix B)

/-- The reflections of `W`: conjugates of simple reflections. -/
def reflections : Set M.Group := {t | ∃ (w : M.Group) (i : B), t = w * M.simple i * w⁻¹}

variable {M}

/-- A reflection-preserving automorphism of `W`. -/
def IsReflPres (β : M.Group ≃* M.Group) : Prop := ∀ t ∈ reflections M, β t ∈ reflections M

/-- A central twist `w ↦ w f(w)` with `f(w) ∈ Z(W)`. -/
def IsCentralTwist (γ : M.Group ≃* M.Group) : Prop := ∀ w, w⁻¹ * γ w ∈ Subgroup.center M.Group

variable (M)

/-- **Franzsen–Howlett** [FH03, Thm. 31] (for the types considered):
`Aut(W) = R(W) · A(W)`, reflection-preserving automorphisms times central twists. -/
def FranzsenHowlett : Prop :=
  ∀ α : M.Group ≃* M.Group, ∃ β γ : M.Group ≃* M.Group, IsReflPres β ∧ IsCentralTwist γ ∧
    ∀ w, α w = β (γ w)

end FHdef

/-! ### The automorphism of `W` induced by an automorphism of `A` -/

namespace ArtinGroup

variable {B : Type*} [DecidableEq B] {M : CoxeterMatrix B}

lemma ker_le_ker_toCoxeter_comp [hCP : (pure M).Characteristic] (φ : ArtinGroup M ≃* ArtinGroup M) :
    (toCoxeter M).ker ≤ ((toCoxeter M).comp φ.toMonoidHom).ker := by
  intro a ha
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  exact char_mem (pure M) φ ha

/-- `φ_W : W → W`, `μ a ↦ μ (φ a)`. -/
noncomputable def coxHom [(pure M).Characteristic] (φ : ArtinGroup M ≃* ArtinGroup M) :
    M.Group →* M.Group :=
  (toCoxeter M).liftOfSurjective toCoxeter_surjective
    ⟨(toCoxeter M).comp φ.toMonoidHom, ker_le_ker_toCoxeter_comp φ⟩

lemma coxHom_apply [(pure M).Characteristic] (φ : ArtinGroup M ≃* ArtinGroup M) (a : ArtinGroup M) :
    coxHom φ (toCoxeter M a) = toCoxeter M (φ a) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a

lemma coxHom_bijective [(pure M).Characteristic] (φ : ArtinGroup M ≃* ArtinGroup M) :
    Bijective (coxHom φ) := by
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨a, rfl⟩ := toCoxeter_surjective x
    rw [coxHom_apply] at hx
    have : φ.symm (φ a) ∈ pure M := char_mem (pure M) φ.symm hx
    simpa [mem_pure] using this
  · intro y
    obtain ⟨b, rfl⟩ := toCoxeter_surjective y
    exact ⟨toCoxeter M (φ.symm b), by rw [coxHom_apply]; simp⟩

/-- The automorphism `φ_W` of `W` induced by `φ ∈ Aut(A)` (uses Cohen–Paris). -/
noncomputable def coxAut [(pure M).Characteristic] (φ : ArtinGroup M ≃* ArtinGroup M) :
    M.Group ≃* M.Group :=
  MulEquiv.ofBijective (coxHom φ) (coxHom_bijective φ)

lemma coxAut_apply [(pure M).Characteristic] (φ : ArtinGroup M ≃* ArtinGroup M) (a : ArtinGroup M) :
    coxAut φ (toCoxeter M a) = toCoxeter M (φ a) := by
  rw [coxAut, MulEquiv.ofBijective_apply, coxHom_apply]

end ArtinGroup

/-! ### Reflection permutations -/

namespace ReflData

variable {B : Type*} [DecidableEq B] {M : CoxeterMatrix B} {T : Type*} [Fintype T] [DecidableEq T]
  (D : ReflData M T)

open ArtinGroup

lemma liftable : M.IsLiftable D.gens := by
  intro i j
  have h := congrArg Aff.toPerm (D.cox2 i j)
  rw [map_pow, map_mul, map_one] at h
  simpa [affGen] using h

/-- `ρ` on the Coxeter group. -/
noncomputable def ρW : M.Group →* Equiv.Perm T := M.toCoxeterSystem.lift ⟨D.gens, D.liftable⟩

lemma ρW_simple (i : B) : D.ρW (M.simple i) = D.gens i := by
  rw [ρW, ← CoxeterMatrix.toCoxeterSystem_simple]
  exact M.toCoxeterSystem.lift_apply_simple D.liftable i

lemma ρ_eq_comp : D.ρ = D.ρW.comp (toCoxeter M) := by
  apply hom_ext
  intro i
  simp [ρW_simple]

lemma ρW_mem (w : M.Group) : D.ρW w ∈ D.ρ.range := by
  obtain ⟨a, rfl⟩ := toCoxeter_surjective w
  exact ⟨a, by rw [ρ_eq_comp]; rfl⟩

lemma gens_inv (i : B) : (D.gens i)⁻¹ = D.gens i := inv_eq_of_mul_eq_one_right (D.gens_sq i)

/-- Explicit reflection permutations `rp t = ρ(t)`, characterised by `rp(s_i) = ρ(s_i)` and
equivariance; injectivity gives `Z(ρ(W)) = 1`. -/
structure RpData where
  rp : T → Equiv.Perm T
  rp_sidx : ∀ i, rp (D.sidx i) = D.gens i
  rp_equiv : ∀ i t, D.gens i * rp t * D.gens i = rp (D.gens i t)
  rp_inj : ∀ a b, rp a = rp b → a = b

variable {D}

lemma RpData.conj (R : D.RpData) {g : Equiv.Perm T} (hg : g ∈ D.ρ.range) (t : T) :
    g * R.rp t * g⁻¹ = R.rp (g t) := by
  revert t
  refine D.range_induction (p := fun g => ∀ t, g * R.rp t * g⁻¹ = R.rp (g t)) ?_ ?_ hg
  · intro t; simp
  · intro i y _ ih t
    rw [mul_inv_rev, D.gens_inv, show D.gens i * y * R.rp t * (y⁻¹ * D.gens i) =
      D.gens i * (y * R.rp t * y⁻¹) * D.gens i by group, ih, R.rp_equiv]
    rfl

lemma RpData.mem (R : D.RpData) (t : T) : R.rp t ∈ D.ρ.range := by
  have ht := D.orb t
  set g := ((D.orbWord t).1.map D.gens).prod
  have hg : g ∈ D.ρ.range := ⟨((D.orbWord t).1.map (σ M)).prod, D.ρ_list_prod _⟩
  rw [← ht, ← R.conj hg, R.rp_sidx]
  exact D.ρ.range.mul_mem (D.ρ.range.mul_mem hg ⟨σ M _, D.ρ_σ _⟩) (D.ρ.range.inv_mem hg)

/-- The centre of `ρ(W)` is trivial. -/
lemma RpData.center_trivial (R : D.RpData) {x : Equiv.Perm T} (hx : x ∈ D.ρ.range)
    (hc : ∀ y ∈ D.ρ.range, x * y = y * x) : x = 1 := by
  ext t
  apply R.rp_inj
  rw [← R.conj hx, hc _ (R.mem t), mul_inv_cancel_right]
  rfl

/-- **Bridge (the induced-automorphism lemma (see lean/DIRECT_PROOF.md)).**  Under Cohen–Paris and Franzsen–Howlett, `ρ(φ(σ_i))` is a reflection
permutation for every `φ ∈ Aut(A)`. -/
theorem RpData.image_refl (R : D.RpData) [(pure M).Characteristic] (hFH : FranzsenHowlett M)
    (φ : ArtinGroup M ≃* ArtinGroup M) (i : B) : ∃ x, D.ρ (φ (σ M i)) = R.rp x := by
  obtain ⟨β, γ, hβ, hγ, hα⟩ := hFH (coxAut φ)
  have h1 : D.ρ (φ (σ M i)) = D.ρW (coxAut φ (M.simple i)) := by
    rw [ρ_eq_comp, MonoidHom.comp_apply, ← coxAut_apply, toCoxeter_σ]
  set z := (M.simple i)⁻¹ * γ (M.simple i)
  have hz : z ∈ Subgroup.center M.Group := hγ _
  have hγs : γ (M.simple i) = M.simple i * z := by simp [z]
  have hβz : β z ∈ Subgroup.center M.Group := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro w
    obtain ⟨w', rfl⟩ := β.surjective w
    rw [← map_mul, ← map_mul, hz]
  have hρz : D.ρW (β z) = 1 := by
    apply R.center_trivial (D.ρW_mem _)
    intro y hy
    obtain ⟨a, rfl⟩ := hy
    rw [ρ_eq_comp, MonoidHom.comp_apply, ← map_mul, ← map_mul,
      (Subgroup.mem_center_iff.mp hβz _).symm]
  obtain ⟨v, j, hv⟩ := hβ (M.simple i) ⟨1, i, by simp⟩
  refine ⟨D.ρW v (D.sidx j), ?_⟩
  rw [h1, hα, hγs, map_mul, map_mul, hρz, mul_one, hv, map_mul, map_mul, map_inv, ρW_simple,
    ← R.rp_sidx, R.conj (D.ρW_mem v)]

end ReflData

/-! ### Search-tree certificates -/

/-- `g` has order exactly `m` (as a `Bool`, for `decide`). -/
def isOrdB {T : Type*} [Fintype T] [DecidableEq T] (g : Equiv.Perm T) (m : ℕ) : Bool :=
  decide (g ^ m = 1) && (List.range m).all (fun d => d == 0 || !decide (g ^ d = 1))

lemma isOrdB_congr {T : Type*} [Fintype T] [DecidableEq T] {g h : Equiv.Perm T}
    (H : ∀ d : ℕ, g ^ d = 1 ↔ h ^ d = 1) (m : ℕ) : isOrdB g m = isOrdB h m := by
  unfold isOrdB
  have e1 : decide (g ^ m = 1) = decide (h ^ m = 1) := by simp [H m]
  have e2 : (fun d => d == 0 || !decide (g ^ d = 1)) = (fun d => d == 0 || !decide (h ^ d = 1)) := by
    funext d; simp [H d]
  rw [e1, e2]

lemma isOrdB_conj {T : Type*} [Fintype T] [DecidableEq T] (g h : Equiv.Perm T) (m : ℕ) :
    isOrdB (h * g * h⁻¹) m = isOrdB g m :=
  isOrdB_congr (fun d => by rw [conj_pow, conj_eq_one_iff]) m

namespace ReflData

variable {n : ℕ} {M : CoxeterMatrix (Fin n)} {T : Type*} [Fintype T] [DecidableEq T]
  (D : ReflData M T)

open ArtinGroup

/-- The Coxeter matrix with natural-number indices. -/
def Mn (M : CoxeterMatrix (Fin n)) (a b : ℕ) : ℕ :=
  if h : a < n ∧ b < n then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

/-- The permutation of a word in the generators. -/
def wordPerm (w : List (Fin n)) : Equiv.Perm T := (w.map D.gens).prod

lemma wordPerm_append (w w' : List (Fin n)) :
    D.wordPerm (w ++ w') = D.wordPerm w * D.wordPerm w' := by
  simp [wordPerm, List.prod_append]

lemma wordPerm_mem (w : List (Fin n)) : D.wordPerm w ∈ D.ρ.range :=
  ⟨(w.map (σ M)).prod, D.ρ_list_prod w⟩

/-- `c` is an admissible next entry after the prefix `p`: the orders of `rp(p_j) rp(c)` are the
Coxeter numbers `m_{j,|p|}`. -/
def validExt (rp : T → Equiv.Perm T) (M : CoxeterMatrix (Fin n)) (p : List T) (c : T) : Bool :=
  (List.range p.length).all fun j =>
    match p[j]? with
    | some a => isOrdB (rp a * rp c) (Mn M j p.length)
    | none => false

/-- A search-tree certificate: nodes are prefixes of representatives; every admissible extension of
a node is moved to the representative of a child node by an explicit element of `ρ(W)` fixing the
prefix; every leaf is the image of the simple reflections under an element of `ρ(W)` or `ρ(W)π₀`. -/
structure TreeCert (R : D.RpData) (π₀ : Equiv.Perm T) where
  K : ℕ
  node : Fin K → List T
  root : Fin K
  root_ok : node root = []
  child : Fin K → T → Fin K
  repF : Fin K → T → T
  hw : Fin K → T → List (Fin n)
  ext_ok : ∀ q c, (node q).length < n → validExt R.rp M (node q) c = true →
    node (child q c) = node q ++ [repF q c] ∧
      (node q).all (fun p => decide (D.wordPerm (hw q c) p = p)) = true ∧
      D.wordPerm (hw q c) (repF q c) = c
  leafW : Fin K → List (Fin n)
  leafE : Fin K → Bool
  leaf_ok : ∀ q, (node q).length = n → ∀ i : Fin n,
    (node q)[i.val]? = some ((D.wordPerm (leafW q) * (if leafE q then π₀ else 1)) (D.sidx i))
  pi0_ok : ∀ t, π₀ * R.rp t * π₀⁻¹ = R.rp (π₀ t)

variable {D}

/-- **Soundness of the search tree**: every tuple of reflections with the Coxeter orders of the
simple reflections is the image of the simple reflections under some `g ∈ ρ(W)` or `g π₀`. -/
theorem TreeCert.conj {R : D.RpData} {π₀ : Equiv.Perm T} (C : D.TreeCert R π₀) (x : Fin n → T)
    (hx : ∀ i j : Fin n, i.val < j.val → isOrdB (R.rp (x i) * R.rp (x j)) (M i j) = true) :
    ∃ (w : List (Fin n)) (e : Bool), ∀ i,
      (D.wordPerm w * (if e then π₀ else 1)) (D.sidx i) = x i := by
  -- invariant after `k` steps
  have key : ∀ k (hk : k ≤ n), ∃ (q : Fin C.K) (w : List (Fin n)), (C.node q).length = k ∧
      ∀ (j : ℕ) (hj : j < k), (C.node q)[j]? =
        some ((D.wordPerm w)⁻¹ (x ⟨j, lt_of_lt_of_le hj hk⟩)) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨C.root, [], by rw [C.root_ok]; rfl, fun j hj => absurd hj (by omega)⟩
    | succ k ih =>
      intro hk
      obtain ⟨q, w, hlen, hq⟩ := ih (by omega)
      set g := D.wordPerm w with hg
      have hgm : g⁻¹ ∈ D.ρ.range := D.ρ.range.inv_mem (D.wordPerm_mem w)
      set c := g⁻¹ (x ⟨k, by omega⟩) with hc
      have hrp : ∀ a, R.rp (g⁻¹ a) = g⁻¹ * R.rp a * g := by
        intro a; rw [← R.conj hgm, inv_inv]
      have hvalid : validExt R.rp M (C.node q) c = true := by
        unfold validExt
        rw [List.all_eq_true]
        intro j hj
        rw [List.mem_range, hlen] at hj
        rw [hq j hj, hlen]
        simp only
        rw [hc, hrp, hrp, show g⁻¹ * R.rp (x ⟨j, by omega⟩) * g * (g⁻¹ * R.rp (x ⟨k, by omega⟩) * g) =
          g⁻¹ * (R.rp (x ⟨j, by omega⟩) * R.rp (x ⟨k, by omega⟩)) * g⁻¹⁻¹ by group, isOrdB_conj]
        have : Mn M j k = M ⟨j, by omega⟩ ⟨k, by omega⟩ := by
          unfold Mn; rw [dif_pos (show j < n ∧ k < n from ⟨by omega, by omega⟩)]
        rw [this]
        exact hx ⟨j, by omega⟩ ⟨k, by omega⟩ hj
      obtain ⟨hnode, hfix, hrep⟩ := C.ext_ok q c (by omega) hvalid
      set h := D.wordPerm (C.hw q c)
      refine ⟨C.child q c, w ++ C.hw q c, by rw [hnode]; simp [hlen], ?_⟩
      intro j hj
      rw [D.wordPerm_append, ← hg, mul_inv_rev, Equiv.Perm.mul_apply, hnode]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · rw [List.getElem?_append_left (by omega), hq j hj']
        congr 1
        have hmem : g⁻¹ (x ⟨j, by omega⟩) ∈ C.node q := by
          exact List.mem_of_getElem? (hq j hj')
        rw [List.all_eq_true] at hfix
        have := of_decide_eq_true (hfix _ hmem)
        rw [eq_comm, Equiv.Perm.inv_eq_iff_eq]
        exact this.symm
      · rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.some.injEq]
        rw [eq_comm, Equiv.Perm.inv_eq_iff_eq, hrep]
  obtain ⟨q, w, hlen, hq⟩ := key n le_rfl
  refine ⟨w ++ C.leafW q, C.leafE q, fun i => ?_⟩
  have h1 := C.leaf_ok q hlen i
  rw [hq i.val i.isLt, Option.some.injEq] at h1
  rw [D.wordPerm_append, mul_assoc, Equiv.Perm.mul_apply, ← h1]
  simp

/-! ### The main theorem with Franzsen–Howlett in place of `hOut` -/

lemma rp_conj_cand {R : D.RpData} {π₀ : Equiv.Perm T} (C : D.TreeCert R π₀) (w : List (Fin n))
    (e : Bool) (t : T) :
    (D.wordPerm w * (if e then π₀ else 1)) * R.rp t * (D.wordPerm w * (if e then π₀ else 1))⁻¹ =
      R.rp ((D.wordPerm w * (if e then π₀ else 1)) t) := by
  cases e
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
    exact R.conj (D.wordPerm_mem w) t
  · simp only [↓reduceIte, mul_inv_rev, Equiv.Perm.mul_apply]
    rw [show D.wordPerm w * π₀ * R.rp t * (π₀⁻¹ * (D.wordPerm w)⁻¹) =
      D.wordPerm w * (π₀ * R.rp t * π₀⁻¹) * (D.wordPerm w)⁻¹ by group, C.pi0_ok,
      R.conj (D.wordPerm_mem w)]

variable (D)

/-- **Main theorem for a type given by explicit data, Franzsen–Howlett version.**
The hypotheses `hW`, `hCP`, `hBr`, `hFH` are cited theorems; `R`, `C`, `hord`, `hInner`, `hOuter` are
finite certificates. -/
theorem rinf_FH (R : D.RpData) (π₀ : Equiv.Perm T) (C : D.TreeCert R π₀)
    (hord : ∀ i j : Fin n, i.val < j.val → isOrdB (D.gens i * D.gens j) (M i j) = true)
    (hW : Finite M.Group) (hCP : (pure M).Characteristic)
    (hBr : Nonempty (Abelianization (pure M) ≃* Multiplicative (T → ℤ)))
    (hFH : FranzsenHowlett M)
    (hInner : Witness D.ρ 1) (hOuter : Witness D.ρ π₀) :
    ∀ φ : ArtinGroup M ≃* ArtinGroup M, reidemeisterAut φ = ⊤ := by
  have := hW
  have := hCP
  have : (pure M).FiniteIndex := pure_finiteIndex (M := M)
  set E := D.permModuleIso hBr
  intro φ
  choose x hx using fun i => R.image_refl hFH φ i
  -- orders of products are preserved
  have hpow : ∀ (a : ArtinGroup M) (d : ℕ), D.ρ (φ a) ^ d = 1 ↔ D.ρ a ^ d = 1 := by
    intro a d
    rw [← map_pow, ← map_pow, ← map_pow]
    constructor
    · intro h
      have := rho_map_eq_one E φ.symm h
      simpa using this
    · exact rho_map_eq_one E φ
  have hxo : ∀ i j : Fin n, i.val < j.val → isOrdB (R.rp (x i) * R.rp (x j)) (M i j) = true := by
    intro i j hij
    rw [← hx i, ← hx j, ← map_mul, ← map_mul, isOrdB_congr (hpow _) (M i j), map_mul, D.ρ_σ, D.ρ_σ]
    exact hord i j hij
  obtain ⟨w, e, hwe⟩ := C.conj x hxo
  set Cp := D.wordPerm w * (if e then π₀ else 1) with hCp
  have hπ : ∀ a, D.ρ (φ a) = Cp * D.ρ a * Cp⁻¹ := by
    have : D.ρ.comp φ.toMonoidHom = (MulAut.conj Cp).toMonoidHom.comp D.ρ := by
      apply hom_ext
      intro i
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, D.ρ_σ]
      rw [hx i, ← hwe i, ← rp_conj_cand C w e, R.rp_sidx]
    intro a
    have := congrArg (fun f => f a) this
    simpa using this
  apply reidemeister_eq_top_of_witness E φ Cp hπ
  have hb : D.wordPerm w = D.ρ (w.map (σ M)).prod := (D.ρ_list_prod w).symm
  cases e
  · have := hInner.mul_left (w.map (σ M)).prod
    simpa [hCp, hb] using this
  · have := hOuter.mul_left (w.map (σ M)).prod
    simpa [hCp, hb] using this

end ReflData

end ArtinRinf
