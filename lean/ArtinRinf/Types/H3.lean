/-
# Type H₃: the finite certificates, checked by `decide`, and the final theorem
-/
import ArtinRinf.Certificate
import ArtinRinf.Data.H3

namespace ArtinRinf.H3

open H3Data ArtinGroup

noncomputable section

/-- The Coxeter matrix `H₃` (Mathlib's). -/
abbrev M : CoxeterMatrix (Fin 3) := CoxeterMatrix.H₃

theorem gensFun_invol : ∀ i x, gensFun i (gensFun i x) = x := by decide +kernel

/-- The permutation of the 15 reflections induced by `s_i`. -/
def gens (i : Fin 3) : Equiv.Perm (Fin 15) :=
  ⟨gensFun i, gensFun i, gensFun_invol i, gensFun_invol i⟩

set_option maxRecDepth 100000 in
/-- The reflection data of `H₃`; every field is checked by `decide`. -/
def D : ReflData M (Fin 15) where
  gens := gens
  sidx := sidx
  gens_sq := by decide +kernel
  gens_fix := by decide +kernel
  braid := by decide +kernel
  cox2 := by decide +kernel
  orbWord := orbWord
  orb := by decide +kernel

theorem pi0Fun_invol : ∀ x, pi0Fun (pi0Fun x) = x := by decide +kernel

/-- The outer permutation `π₀` of the reflections (Galois conjugation `√5 ↦ -√5` followed by a
coordinate permutation; paper, Appendix B). -/
def pi0 : Equiv.Perm (Fin 15) := ⟨pi0Fun, pi0Fun, pi0Fun_invol, pi0Fun_invol⟩

/-- Sanity check: `π₀` normalises `ρ(W)`, i.e. `π₀ ρ(s_i) π₀⁻¹ ∈ ρ(W)` with explicit words.
(Not needed for the main theorem; it shows the hypothesis `hOut` is about a genuine element of
the normaliser.) -/
theorem pi0_normalises : ∀ i, pi0 * gens i * pi0⁻¹ = ((pi0ConjWord i).map gens).prod := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The orbital certificate. -/
def C : OrbitalCert gens 6 where
  lab := lab
  rep := rep
  par := par
  depth := depth
  ok_none := by decide +kernel
  ok_some := by decide +kernel

set_option maxRecDepth 100000 in
/-- **Good constituent** (dimension 4): every matrix commuting with `ρ(W)` acts on `U` by a scalar. -/
theorem commScalar_U0 : CommScalar D.ρ (spanZ U0) :=
  commScalar_of_cert D.ρ gens D.hgen C U0 mu0 (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Witnesses for the trivial outer class (`π = 1`). -/
theorem witness_inner : Witness D.ρ 1 :=
  Or.inl ⟨_, commScalar_U0, D.stableWitness 1 U0 [] [innerMinusGen] innerPlusC innerMinusC
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
/-- Witnesses for the nontrivial outer class (`π = π₀`; stable case). -/
theorem witness_outer : Witness D.ρ pi0 :=
  Or.inl ⟨_, commScalar_U0, D.stableWitness pi0 U0 outerPlusWord outerMinusWord outerPlusC
    outerMinusC (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

/-- **Main theorem for `H₃`.**  Every automorphism of the Artin group of type `H₃` has infinitely
many twisted conjugacy classes, assuming
* `hW`: the Coxeter group `W(H₃)` is finite (classical);
* `hCP`: the pure Artin group is characteristic (Cohen–Paris, Thm 1.4; computer-assisted);
* `hBr`: `H₁(P;ℤ) ≅ ℤ^15` (Brieskorn; Orlik–Terao; 15 = number of reflections);
* `hOut`: every automorphism of `ρ(W) ≅ W/Z(W)` is conjugation by an element of `ρ(W)` or of
  `ρ(W)π₀` (computed: `|Out(W/Z)| = 2`, paper Appendix B). -/
theorem artin_H3_R_infty (hW : Finite M.Group) (hCP : (pure M).Characteristic)
    (hBr : Nonempty (Abelianization (pure M) ≃* Multiplicative (Fin 15 → ℤ)))
    (hOut : OutGeneratedBy D.ρ.range pi0) :
    ∀ φ : ArtinGroup M ≃* ArtinGroup M, reidemeisterAut φ = ⊤ :=
  D.rinf hW hCP hBr pi0 hOut witness_inner witness_outer

end

end ArtinRinf.H3
