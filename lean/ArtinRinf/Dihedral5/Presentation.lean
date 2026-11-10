/- The presented Artin group of type I₂(5) and its ten Schreier cosets. -/
import ArtinRinf.ArtinGroup
import ArtinRinf.SchreierKernel
import ArtinRinf.Dihedral5.Generators

namespace ArtinRinf.Dihedral5
namespace Presentation

open DihedralGroup ArtinGroup

/-- Mathlib's parameter is shifted by two: I 3 is I₂(5). -/
abbrev M : CoxeterMatrix (Fin 2) := CoxeterMatrix.I 3
abbrev A := ArtinGroup M
abbrev gen (i : Fin 2) : A := σ M i

def affineGen : Fin 2 → Gamma := ![a, b]

lemma affine_braid : ∀ i j : Fin 2, i ≠ j →
    braidWord (affineGen i) (affineGen j) (M i j) =
      braidWord (affineGen j) (affineGen i) (M i j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> try contradiction
  · simpa [M, CoxeterMatrix.I, affineGen, braidWord, mul_assoc] using braid_relation
  · simpa [M, CoxeterMatrix.I, affineGen, braidWord, mul_assoc] using braid_relation.symm

def toGamma : A →* Gamma := ArtinGroup.lift affineGen affine_braid

@[simp] lemma toGamma_gen (i : Fin 2) : toGamma (gen i) = affineGen i := lift_σ _ _ i

def holonomy : Gamma →* Hol where
  toFun x := x.val.g
  map_one' := rfl
  map_mul' _ _ := rfl

def toHol : A →* Hol := holonomy.comp toGamma
def holGen : Fin 2 → Hol := ![sr 0, sr 3]

@[simp] lemma toHol_gen (i : Fin 2) : toHol (gen i) = holGen i := by
  fin_cases i <;> rfl

def hol : Fin 10 → Hol := ![r 0, sr 0, sr 3, r 3, r 2, sr 2, sr 1, r 1, r 4, sr 4]
def index : Hol → Fin 10
  | r k => (![0, 7, 4, 3, 8] : Fin 5 → Fin 10) ⟨k.val, ZMod.val_lt k⟩
  | sr k => (![1, 6, 5, 2, 9] : Fin 5 → Fin 10) ⟨k.val, ZMod.val_lt k⟩

lemma hol_index : ∀ g, hol (index g) = g := by decide +kernel
lemma index_hol : ∀ j, index (hol j) = j := by decide +kernel

def words : Fin 10 → List (Fin 2) :=
  ![[], [0], [1], [0,1], [1,0], [0,1,0], [1,0,1], [0,1,0,1], [1,0,1,0], [0,1,0,1,0]]

def eval (w : List (Fin 2)) : A := (w.map gen).prod
def secLift (g : Hol) : A := eval (words (index g))

lemma words_hol : ∀ j, ((words j).map holGen).prod = hol j := by decide +kernel

lemma section_hol (g : Hol) : toHol (secLift g) = g := by
  simp only [secLift, eval, map_list_prod, List.map_map, Function.comp_def, toHol_gen]
  rw [words_hol, hol_index]

lemma section_one : secLift 1 = 1 := rfl

abbrev P := toHol.ker
def edge (j : Fin 10) (i : Fin 2) : P :=
  SchreierKernel.edge toHol secLift section_hol gen (hol j) i

def next (j : Fin 10) (i : Fin 2) : Fin 10 := index (hol j * holGen i)

lemma edge_val (j : Fin 10) (i : Fin 2) :
    (edge j i).val = eval (words j) * gen i * (eval (words (next j i)))⁻¹ := by
  simp [edge, SchreierKernel.edge, secLift, index_hol, next]

lemma gens_generate : Subgroup.closure (Set.range gen) = ⊤ :=
  PresentedGroup.closure_range_of _

lemma edges_generate : Subgroup.closure (Set.range (fun p : Fin 10 × Fin 2 => edge p.1 p.2)) = ⊤ := by
  have h := SchreierKernel.closure_edges toHol secLift section_hol gen section_one gens_generate
  apply top_unique
  rw [← h, Subgroup.closure_le]
  rintro _ ⟨⟨g, i⟩, rfl⟩
  apply Subgroup.subset_closure
  exact ⟨(index g, i), by simp [edge, hol_index]⟩

lemma next_table : next =
    ![![1,2], ![0,3], ![4,0], ![5,1], ![2,6], ![3,7], ![8,4], ![9,5], ![6,9], ![7,8]] := by
  decide +kernel

def finish : Fin 10 → List (Fin 2) → Fin 10
  | j, [] => j
  | j, i :: w => finish (next j i) w

def path : Fin 10 → List (Fin 2) → P
  | _, [] => 1
  | j, i :: w => edge j i * path (next j i) w

lemma path_val (j : Fin 10) (w : List (Fin 2)) :
    (path j w).val = eval (words j) * eval w * (eval (words (finish j w)))⁻¹ := by
  induction w generalizing j with
  | nil => simp [path, eval, finish]
  | cons i w ih =>
    simp only [path, Subgroup.coe_mul, edge_val, ih, finish]
    have he : eval (i :: w) = gen i * eval w := rfl
    rw [he]
    group

lemma artin_braid : eval [0,1,0,1,0] = eval [1,0,1,0,1] := by
  have h := ArtinGroup.braid (M := M) 0 1
  change braidWord (gen 0) (gen 1) 5 = braidWord (gen 1) (gen 0) 5 at h
  simpa only [braidWord, eval, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] using h

lemma braid_path (j : Fin 10) : path j [0,1,0,1,0] = path j [1,0,1,0,1] := by
  have he : ∀ j, finish j [0,1,0,1,0] = finish j [1,0,1,0,1] := by decide +kernel
  apply Subtype.ext
  rw [path_val, path_val, artin_braid, he]

lemma trivial_edges : edge 0 0 = 1 ∧ edge 0 1 = 1 ∧ edge 1 1 = 1 ∧
    edge 2 0 = 1 ∧ edge 3 0 = 1 ∧ edge 4 1 = 1 ∧ edge 5 1 = 1 ∧
    edge 6 0 = 1 ∧ edge 7 0 = 1 ∧ edge 8 1 = 1 := by
  have hb := artin_braid
  simp only [eval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one] at hb
  repeat' constructor
  all_goals apply Subtype.ext
  all_goals rw [edge_val]
  all_goals norm_num [next_table, words, eval]
  all_goals first
    | solve | group
    | convert mul_inv_eq_one.mpr hb.symm using 1; group

/-- Five explicit pure meridians, indexed by their translation coordinate. -/
def meridian : I → P := ![edge 1 0, edge 2 1, edge 4 0, edge 5 0, edge 3 1]

theorem meridians_generate : Subgroup.closure (Set.range meridian) = ⊤ := by
  let K := Subgroup.closure (Set.range meridian)
  have hm (i : I) : meridian i ∈ K := Subgroup.subset_closure ⟨i, rfl⟩
  have h10 : edge 1 0 ∈ K := hm 0
  have h21 : edge 2 1 ∈ K := hm 1
  have h40 : edge 4 0 ∈ K := hm 2
  have h50 : edge 5 0 ∈ K := hm 3
  have h31 : edge 3 1 ∈ K := hm 4
  have h1 := braid_path 1
  have h2 := braid_path 2
  have h3 := braid_path 3
  have h4 := braid_path 4
  have h5 := braid_path 5
  norm_num [path, next_table, trivial_edges] at h1 h2 h3 h4 h5
  have h91 : edge 9 1 ∈ K := by rw [← h1]; exact h10
  have h90 : edge 9 0 ∈ K := by rw [h2]; exact h21
  have h80 : edge 8 0 ∈ K := (K.mul_mem_cancel_left h91).mp (by rw [h3]; exact K.mul_mem h31 h10)
  have h71 : edge 7 1 ∈ K := (K.mul_mem_cancel_left h90).mp (by rw [← h4]; exact K.mul_mem h40 h21)
  have h61 : edge 6 1 ∈ K := (K.mul_mem_cancel_left h80).mp
    ((K.mul_mem_cancel_left h91).mp (by rw [← h5]; exact K.mul_mem h50 (K.mul_mem h31 h10)))
  apply top_unique
  rw [← edges_generate, Subgroup.closure_le]
  rintro _ ⟨⟨j, i⟩, rfl⟩
  fin_cases j <;> fin_cases i <;>
    simp_all [trivial_edges, K]

theorem toGamma_surjective : Function.Surjective toGamma := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← generated_eq_top, generated, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact ⟨gen 0, by simp [affineGen]⟩
  · exact ⟨gen 1, by simp [affineGen]⟩

end Presentation
end ArtinRinf.Dihedral5
