/-
# Type F₄: the finite certificates, checked by `decide`, and the final theorem
-/
import ArtinRinf.Certificate
import ArtinRinf.Data.F4

namespace ArtinRinf.F4

open F4Data ArtinGroup

noncomputable section

/-- The Coxeter matrix `F₄` (Mathlib's). -/
abbrev M : CoxeterMatrix (Fin 4) := CoxeterMatrix.F₄

theorem gensFun_invol : ∀ i x, gensFun i (gensFun i x) = x := by decide +kernel

/-- The permutation of the 24 reflections induced by `s_i`. -/
def gens (i : Fin 4) : Equiv.Perm (Fin 24) :=
  ⟨gensFun i, gensFun i, gensFun_invol i, gensFun_invol i⟩

set_option maxRecDepth 100000 in
/-- The reflection data of `F₄`; every field is checked by `decide`. -/
def D : ReflData M (Fin 24) where
  gens := gens
  sidx := sidx
  gens_sq := by decide +kernel
  gens_fix := by decide +kernel
  braid := by decide +kernel
  cox2 := by decide +kernel
  orbWord := orbWord
  orb := by decide +kernel

theorem pi0Fun_invol : ∀ x, pi0Fun (pi0Fun x) = x := by decide +kernel

/-- The outer permutation `π₀` of the reflections induced by the similarity
`L(x) = (x₁+x₂, x₁-x₂, x₃+x₄, x₃-x₄)`, exchanging long and short roots; paper, Proposition 4.1(b)). -/
def pi0 : Equiv.Perm (Fin 24) := ⟨pi0Fun, pi0Fun, pi0Fun_invol, pi0Fun_invol⟩

/-- Sanity check: `π₀` normalises `ρ(W)`, i.e. `π₀ ρ(s_i) π₀⁻¹ ∈ ρ(W)` with explicit words.
(Not needed for the main theorem; it shows the hypothesis `hOut` is about a genuine element of
the normaliser.) -/
theorem pi0_normalises : ∀ i, pi0 * gens i * pi0⁻¹ = ((pi0ConjWord i).map gens).prod := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The orbital certificate. -/
def C : OrbitalCert gens 10 where
  lab := lab
  rep := rep
  par := par
  depth := depth
  ok_none := by decide +kernel
  ok_some := by decide +kernel

set_option maxRecDepth 100000 in
/-- **Good constituent** `U_long` (dimension 2). -/
theorem commScalar_U0 : CommScalar D.ρ (spanZ U0) :=
  commScalar_of_cert D.ρ gens D.hgen C U0 mu0 (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **Good constituent** `U_short` (dimension 2). -/
theorem commScalar_U1 : CommScalar D.ρ (spanZ U1) :=
  commScalar_of_cert D.ρ gens D.hgen C U1 mu1 (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Witnesses for the trivial outer class (`π = 1`; stable case on `U_long`). -/
theorem witness_inner : Witness D.ρ 1 :=
  Or.inl ⟨_, commScalar_U0, D.stableWitness 1 U0 [] [innerMinusGen] innerPlusC innerMinusC
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
/-- Witnesses for the nontrivial outer class (`π = π₀`; **swap case**: `π₀` exchanges
`U_long` and `U_short`). -/
theorem witness_outer : Witness D.ρ pi0 :=
  Or.inr ⟨_, _, commScalar_U0, commScalar_U1,
    D.swapWitness pi0 U0 U1 outerPlusWord outerMinusWord outerPlusC outerMinusC outerPlusC2
      outerMinusC2 (by decide +kernel) (by decide +kernel)⟩

/-- **Main theorem for `F₄`.**  Every automorphism of the Artin group of type `F₄` has infinitely
many twisted conjugacy classes, assuming
* `hW`: the Coxeter group `W(F₄)` is finite (classical);
* `hCP`: the pure Artin group is characteristic (Cohen–Paris, Thm 1.4; computer-assisted);
* `hBr`: `H₁(P;ℤ) ≅ ℤ^24` (Brieskorn; Orlik–Terao; 24 = number of reflections);
* `hOut`: every automorphism of `ρ(W) ≅ W/Z(W)` is conjugation by an element of `ρ(W)` or of
  `ρ(W)π₀` (computed: `|Out(W/Z)| = 2`, paper Proposition 4.1(b)). -/
theorem artin_F4_R_infty (hW : Finite M.Group) (hCP : (pure M).Characteristic)
    (hBr : Nonempty (Abelianization (pure M) ≃* Multiplicative (Fin 24 → ℤ)))
    (hOut : OutGeneratedBy D.ρ.range pi0) :
    ∀ φ : ArtinGroup M ≃* ArtinGroup M, reidemeisterAut φ = ⊤ :=
  D.rinf hW hCP hBr pi0 hOut witness_inner witness_outer

end

end ArtinRinf.F4
