/-
# Type F₄: `Out(ρ(W))` verified in Lean by enumeration

This removes the hypothesis `hOut` from the `F₄` theorem: the remaining hypotheses are exactly the
cited theorems (finiteness of `W`, Cohen–Paris, Brieskorn).

Method: `ρ(W) ≅ W(F₄)/{±1}` has 576 elements and 75 involutions.  An automorphism `θ` is
determined by the images of the four generators, which form a tuple of involutions whose
pairwise products have the same orders as for the generators.  There are exactly 1152 such tuples
(found with the help of the precomputed tables `rel2`, `rel3`, `rel4`, whose completeness is
checked), and each is conjugate to the generators by an element of `ρ(W)` or `ρ(W)π₀`.
-/
import ArtinRinf.OutCert
import ArtinRinf.Types.F4
import ArtinRinf.Data.F4Out

set_option maxHeartbeats 0

namespace ArtinRinf.F4

open F4Out ArtinGroup

noncomputable section

theorem elt_inv1 : ∀ k x, eltInvFun k (eltFun k x) = x := by decide +kernel
theorem elt_inv2 : ∀ k x, eltFun k (eltInvFun k x) = x := by decide +kernel

/-- The 576 elements of `ρ(W(F₄))`. -/
def elt (k : Fin 576) : Equiv.Perm (Fin 24) := ⟨eltFun k, eltInvFun k, elt_inv1 k, elt_inv2 k⟩

theorem word_ok : ∀ k, elt k = ((word k).map D.gens).prod := by decide +kernel
theorem one_ok : elt 0 = 1 := by decide +kernel
theorem mul_ok : ∀ i k, D.gens i * elt k = elt (mulTab i k) := by decide +kernel

/-- The list of involutions. -/
def invIdx : List (Fin 576) := List.ofFn invL

theorem inv_ok' : ∀ k, elt k * elt k = 1 → elt k ≠ 1 → ∃ a, invL a = k := by decide +kernel
theorem inv_ok : ∀ k, elt k * elt k = 1 → elt k ≠ 1 → k ∈ invIdx := by
  intro k h1 h2
  obtain ⟨a, ha⟩ := inv_ok' k h1 h2
  rw [invIdx, List.mem_ofFn]
  exact ⟨a, ha⟩

theorem gens_ne : ∀ i j : Fin 4, i ≠ j → D.gens i ≠ D.gens j := by decide +kernel
theorem gens_ne_one : ∀ i : Fin 4, D.gens i ≠ 1 := by decide +kernel
theorem gens_rel : ∀ i j, (D.gens i * D.gens j) ^ (M i j) = 1 := by decide +kernel
theorem M_lt' : ∀ i j : Fin 4, Nat.blt (M i j) 6 = true := by decide +kernel
theorem M_lt (i j : Fin 4) : M i j < 6 := Nat.blt_eq.mp (M_lt' i j)
theorem gens_ord' : ∀ i j : Fin 4, ∀ d : Fin 6, 0 < d.val → d.val < M i j →
    (D.gens i * D.gens j) ^ d.val ≠ 1 := by
  decide +kernel
theorem gens_ord (i j : Fin 4) (d : ℕ) (hd : 0 < d) (hdm : d < M i j) :
    (D.gens i * D.gens j) ^ d ≠ 1 :=
  gens_ord' i j ⟨d, lt_trans hdm (M_lt i j)⟩ hd hdm

/-- Completeness of the relation tables. -/
theorem rel2_ok : ∀ a b, elt (invL a) ≠ elt (invL b) →
    (elt (invL a) * elt (invL b)) ^ 2 = 1 → rel2 a b = true := by decide +kernel
theorem rel3_ok : ∀ a b, elt (invL a) ≠ elt (invL b) →
    (elt (invL a) * elt (invL b)) ^ 3 = 1 → rel3 a b = true := by decide +kernel
theorem rel4_ok : ∀ a b, (elt (invL a) * elt (invL b)) ^ 4 = 1 →
    (elt (invL a) * elt (invL b)) ^ 2 ≠ 1 → rel4 a b = true := by decide +kernel

/-- The conjugator `elt k` or `elt k * π₀`. -/
def cand (k : Fin 576) (b : Bool) : Equiv.Perm (Fin 24) := if b then elt k * pi0 else elt k

/-- The core finite check: each of the Coxeter-like tuples (pruned with the relation tables) is
conjugate to the generators by the tabulated element of `ρ(W) ∪ ρ(W)π₀`. -/
theorem check_concrete : ∀ a b, rel3 a b = true → ∀ c, rel2 a c = true → rel4 b c = true →
    ∀ d, rel2 a d = true → rel2 b d = true → rel3 c d = true →
      cand (conjOf a b c d).1 (conjOf a b c d).2 * D.gens 0 *
          (cand (conjOf a b c d).1 (conjOf a b c d).2)⁻¹ = elt (invL a) ∧
      cand (conjOf a b c d).1 (conjOf a b c d).2 * D.gens 1 *
          (cand (conjOf a b c d).1 (conjOf a b c d).2)⁻¹ = elt (invL b) ∧
      cand (conjOf a b c d).1 (conjOf a b c d).2 * D.gens 2 *
          (cand (conjOf a b c d).1 (conjOf a b c d).2)⁻¹ = elt (invL c) ∧
      cand (conjOf a b c d).1 (conjOf a b c d).2 * D.gens 3 *
          (cand (conjOf a b c d).1 (conjOf a b c d).2)⁻¹ = elt (invL d) := by
  decide +kernel

/-- The enumeration certificate for `Out(ρ(W(F₄)))`. -/
def outCert : ReflData.OutCert D pi0 576 where
  elt := elt
  word := word
  word_ok := word_ok
  one_idx := 0
  one_ok := one_ok
  mulTab := mulTab
  mul_ok := mul_ok
  invIdx := invIdx
  inv_ok := inv_ok
  gens_ne := gens_ne
  gens_ne_one := gens_ne_one
  gens_rel := gens_rel
  gens_ord := gens_ord
  check := by
    intro y hy hd hr ho
    have hy' : ∀ i, ∃ a, invL a = y i := fun i => by
      have := hy i
      rw [invIdx, List.mem_ofFn] at this
      exact this
    choose a ha using hy'
    have e : ∀ i, elt (y i) = elt (invL (a i)) := fun i => by rw [ha i]
    simp only [e] at hd hr ho
    have h01 := rel3_ok (a 0) (a 1) (hd 0 1 (by decide)) (hr 0 1)
    have h02 := rel2_ok (a 0) (a 2) (hd 0 2 (by decide)) (hr 0 2)
    have h12 := rel4_ok (a 1) (a 2) (hr 1 2) (ho 1 2 2 (by decide) (by decide))
    have h03 := rel2_ok (a 0) (a 3) (hd 0 3 (by decide)) (hr 0 3)
    have h13 := rel2_ok (a 1) (a 3) (hd 1 3 (by decide)) (hr 1 3)
    have h23 := rel3_ok (a 2) (a 3) (hd 2 3 (by decide)) (hr 2 3)
    obtain ⟨c0, c1, c2, c3⟩ := check_concrete (a 0) (a 1) h01 (a 2) h02 h12 (a 3) h03 h13 h23
    refine ⟨(conjOf (a 0) (a 1) (a 2) (a 3)).1, (conjOf (a 0) (a 1) (a 2) (a 3)).2, ?_⟩
    intro i
    rw [e i]
    fin_cases i
    · exact c0
    · exact c1
    · exact c2
    · exact c3

/-- `Out(ρ(W(F₄)))` is generated by `π₀` — verified in Lean (paper, Proposition 4.1(b)). -/
theorem hOut : OutGeneratedBy D.ρ.range pi0 := outCert.outGeneratedBy

/-- **Main theorem for `F₄`, with `Out(W/Z)` verified in Lean.**  The only hypotheses are the
cited theorems: `W(F₄)` finite, Cohen–Paris (`P` characteristic), Brieskorn (`H₁(P) ≅ ℤ^24`). -/
theorem artin_F4_R_infty' (hW : Finite M.Group) (hCP : (pure M).Characteristic)
    (hBr : Nonempty (Abelianization (pure M) ≃* Multiplicative (Fin 24 → ℤ))) :
    ∀ φ : ArtinGroup M ≃* ArtinGroup M, reidemeisterAut φ = ⊤ :=
  artin_F4_R_infty hW hCP hBr hOut

end

end ArtinRinf.F4
