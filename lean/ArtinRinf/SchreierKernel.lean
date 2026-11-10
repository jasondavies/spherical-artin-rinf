/- Schreier generators for the kernel of a homomorphism with a chosen section. -/
import Mathlib

namespace ArtinRinf

namespace SchreierKernel

variable {G H B : Type*} [Group G] [Group H]
variable (f : G →* H) (s : H → G) (hs : ∀ h, f (s h) = h)

def normal (x : G) : f.ker :=
  ⟨x * (s (f x))⁻¹, by simp [MonoidHom.mem_ker, hs]⟩

def edge (gen : B → G) (h : H) (i : B) : f.ker :=
  ⟨s h * gen i * (s (h * f (gen i)))⁻¹, by simp [MonoidHom.mem_ker, hs]⟩

lemma normal_mul (gen : B → G) (x : G) (i : B) :
    normal f s hs (x * gen i) = normal f s hs x * edge f s hs gen (f x) i := by
  apply Subtype.ext
  simp only [normal, edge, Subgroup.coe_mul, map_mul]
  group

lemma normal_mul_inv (gen : B → G) (x : G) (i : B) :
    normal f s hs (x * (gen i)⁻¹) =
      normal f s hs x * (edge f s hs gen (f x * (f (gen i))⁻¹) i)⁻¹ := by
  apply Subtype.ext
  simp only [normal, edge, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
    inv_mul_cancel_right]
  group

/-- A section and generators of G give a complete generating family for ker f. -/
theorem closure_edges (gen : B → G) (hs1 : s 1 = 1)
    (hgen : Subgroup.closure (Set.range gen) = ⊤) :
    Subgroup.closure (Set.range (fun p : H × B => edge f s hs gen p.1 p.2)) = ⊤ := by
  let K := Subgroup.closure (Set.range (fun p : H × B => edge f s hs gen p.1 p.2))
  have hn (x : G) : normal f s hs x ∈ K := by
    have hx : x ∈ Subgroup.closure (Set.range gen) := by rw [hgen]; trivial
    induction hx using Subgroup.closure_induction_right with
    | one =>
      have he : normal f s hs (1 : G) = 1 := by
        apply Subtype.ext
        simp [normal, hs1]
      rw [he]; exact K.one_mem
    | mul_right x _ y hy hx =>
      obtain ⟨i, rfl⟩ := hy
      rw [normal_mul]
      exact K.mul_mem hx (Subgroup.subset_closure ⟨(f x, i), rfl⟩)
    | mul_inv_cancel x _ y hy hx =>
      obtain ⟨i, rfl⟩ := hy
      rw [normal_mul_inv]
      exact K.mul_mem hx (K.inv_mem (Subgroup.subset_closure ⟨(f x * (f (gen i))⁻¹, i), rfl⟩))
  apply top_unique
  intro x _
  have he : normal f s hs x.val = x := by
    apply Subtype.ext
    simp [normal, show f x.val = 1 from x.property, hs1]
  rw [← he]
  exact hn x.val

end SchreierKernel
end ArtinRinf
