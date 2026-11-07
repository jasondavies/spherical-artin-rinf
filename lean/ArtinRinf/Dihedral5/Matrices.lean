/- Exact arithmetic certificates for I₂(5). Verified by the Lean kernel. -/
import ArtinRinf.Dihedral5.Data
open Matrix
namespace ArtinRinf.Dihedral5

def D : Matrix I I ℤ := ![![1, (-1), 0, 0, (-1)],
    ![(-1), 1, (-1), 0, 0],
    ![0, (-1), 1, (-1), 0],
    ![0, 0, (-1), 1, (-1)],
    ![(-1), 0, 0, (-1), 1]]
def Dinv : Matrix I I ℤ := ![![1, 0, (-1), (-1), 0],
    ![0, 1, 0, (-1), (-1)],
    ![(-1), 0, 1, 0, (-1)],
    ![(-1), (-1), 0, 1, 0],
    ![0, (-1), (-1), 0, 1]]
def displacement : V := ![1, 1, 0, 0, 0]

theorem Dinv_D : Dinv * D = 1 := by decide +kernel
theorem D_Dinv : D * Dinv = 1 := by decide +kernel
theorem D_comm : ∀ g, D * pmat ℤ (perm g) = pmat ℤ (perm g) * D := by decide +kernel

def correctionRot : Fin 5 → V := ![![0, 0, 0, 0, 0],
    ![0, (-1), (-1), (-1), (-1)],
    ![0, 0, (-1), (-1), 0],
    ![0, 0, 0, (-1), (-1)],
    ![(-1), 0, (-1), (-1), (-1)]]
def correctionRef : Fin 5 → V := ![![0, 0, 0, 0, (-1)],
    ![0, 0, (-1), (-1), (-1)],
    ![0, 0, (-1), (-1), (-1)],
    ![0, 0, (-1), 0, 0],
    ![(-1), (-1), (-1), (-1), (-1)]]
def correction : Hol → V
  | DihedralGroup.r k => correctionRot ⟨k.val, ZMod.val_lt k⟩
  | DihedralGroup.sr k => correctionRef ⟨k.val, ZMod.val_lt k⟩

def invCorrectionRot : Fin 5 → V := ![![0, 0, 0, 0, 0],
    ![(-2), (-1), 0, 0, (-1)],
    ![(-2), (-1), 1, 1, (-1)],
    ![(-1), (-2), (-1), 1, 1],
    ![(-1), (-2), (-1), 0, 0]]
def invCorrectionRef : Fin 5 → V := ![![0, (-1), (-1), 0, 1],
    ![(-2), (-2), 0, 1, 0],
    ![(-2), (-2), 0, 1, 0],
    ![(-1), 0, 1, 0, (-1)],
    ![(-1), (-1), (-1), (-1), (-1)]]
def invCorrection : Hol → V
  | DihedralGroup.r k => invCorrectionRot ⟨k.val, ZMod.val_lt k⟩
  | DihedralGroup.sr k => invCorrectionRef ⟨k.val, ZMod.val_lt k⟩

theorem correction_spec : ∀ g,
    D *ᵥ offset g + (displacement - pact (perm g) displacement) =
      offset g + 2 • correction g := by decide +kernel
theorem invCorrection_spec : ∀ g, Dinv *ᵥ correction g + invCorrection g = 0 := by decide +kernel
theorem correction_inv_spec : ∀ g, D *ᵥ invCorrection g + correction g = 0 := by decide +kernel

def modulusRot : Fin 5 → ℕ := ![2,
    22,
    22,
    22,
    22]
def modulusRef : Fin 5 → ℕ := ![10,
    10,
    10,
    10,
    10]
def modulus : Hol → ℕ
  | DihedralGroup.r k => modulusRot ⟨k.val, ZMod.val_lt k⟩
  | DihedralGroup.sr k => modulusRef ⟨k.val, ZMod.val_lt k⟩

theorem modulus_pos : ∀ g, 0 < modulus g := by decide +kernel
instance modulusNeZero (g : Hol) : NeZero (modulus g) := ⟨Nat.ne_of_gt (modulus_pos g)⟩
instance modulusFintype (g : Hol) : Fintype (ZMod (modulus g)) := inferInstance

def ellRot : Fin 5 → V := ![![1, 1, 1, 1, 1],
    ![1, 5, 3, 15, 9],
    ![1, 3, 9, 5, 15],
    ![1, 15, 5, 9, 3],
    ![1, 9, 15, 3, 5]]
def ellRef : Fin 5 → V := ![![5, 1, 7, 3, 9],
    ![1, 3, 5, 7, 9],
    ![1, 7, 3, 9, 5],
    ![1, 5, 9, 3, 7],
    ![1, 9, 7, 5, 3]]
def ell : Hol → V
  | DihedralGroup.r k => ellRot ⟨k.val, ZMod.val_lt k⟩
  | DihedralGroup.sr k => ellRef ⟨k.val, ZMod.val_lt k⟩

def pivotRot : Fin 5 → I := ![0,
    0,
    0,
    0,
    0]
def pivotRef : Fin 5 → I := ![1,
    0,
    0,
    0,
    0]
def pivot : Hol → I
  | DihedralGroup.r k => pivotRot ⟨k.val, ZMod.val_lt k⟩
  | DihedralGroup.sr k => pivotRef ⟨k.val, ZMod.val_lt k⟩

def reduceMatrixRot : Fin 5 → Matrix I I ℤ := ![![![0, 0, (-1), (-1), 0],
    ![0, 0, 0, (-1), (-1)],
    ![0, 1, 1, 1, 0],
    ![0, 0, 1, 1, 1],
    ![0, (-1), (-1), 0, 0]],
    ![![0, (-3), (-2), (-9), (-5)],
    ![0, (-1), (-1), (-5), (-3)],
    ![0, 1, 1, 2, 1],
    ![0, 1, 1, 4, 2],
    ![0, 0, 0, 1, 1]],
    ![![0, (-1), (-4), (-2), (-6)],
    ![0, 0, (-1), (-1), (-2)],
    ![0, 0, 0, 0, (-1)],
    ![0, 1, 3, 2, 5],
    ![0, (-1), (-2), (-1), (-3)]],
    ![![0, (-6), (-2), (-4), (-1)],
    ![0, (-3), (-1), (-2), (-1)],
    ![0, 5, 2, 3, 1],
    ![0, (-1), 0, 0, 0],
    ![0, (-2), (-1), (-1), 0]],
    ![![0, (-5), (-9), (-2), (-3)],
    ![0, 1, 1, 0, 0],
    ![0, 2, 4, 1, 1],
    ![0, 1, 2, 1, 1],
    ![0, (-3), (-5), (-1), (-1)]]]
def reduceMatrixRef : Fin 5 → Matrix I I ℤ := ![![![(-2), 0, (-4), (-2), (-4)],
    ![(-1), 0, (-2), (-1), (-3)],
    ![(-1), 0, 0, 0, (-1)],
    ![0, 0, 1, 1, 1],
    ![2, 0, 2, 1, 3]],
    ![![0, (-2), (-4), (-5), (-6)],
    ![0, 0, 0, (-1), (-1)],
    ![0, 2, 3, 4, 4],
    ![0, 0, 1, 1, 1],
    ![0, (-1), (-2), (-2), (-2)]],
    ![![0, (-2), (-1), (-3), (-1)],
    ![0, 0, 0, (-1), (-1)],
    ![0, 1, 1, 1, 0],
    ![0, 2, 1, 3, 2],
    ![0, (-4), (-2), (-4), (-2)]],
    ![![0, (-1), (-3), (-1), (-2)],
    ![0, (-2), (-4), (-2), (-4)],
    ![0, 2, 3, 1, 2],
    ![0, 0, 1, 1, 1],
    ![0, (-1), (-1), 0, 0]],
    ![![0, (-6), (-5), (-4), (-2)],
    ![0, (-2), (-2), (-2), (-1)],
    ![0, 1, 1, 1, 0],
    ![0, 4, 4, 3, 2],
    ![0, (-1), (-1), 0, 0]]]
def reduceMatrix : Hol → Matrix I I ℤ
  | DihedralGroup.r k => reduceMatrixRot ⟨k.val, ZMod.val_lt k⟩
  | DihedralGroup.sr k => reduceMatrixRef ⟨k.val, ZMod.val_lt k⟩

def reduceVectorRot : Fin 5 → V := ![![1, 1, (-1), (-1), 1],
    ![13, 7, (-3), (-5), (-1)],
    ![9, 3, 1, (-7), 5],
    ![9, 5, (-7), 1, 3],
    ![13, (-1), (-5), (-3), 7]]
def reduceVectorRef : Fin 5 → V := ![![5, 3, 1, (-1), (-3)],
    ![7, 1, (-5), (-1), 3],
    ![3, 1, (-1), (-3), 5],
    ![3, 5, (-3), (-1), 1],
    ![7, 3, (-1), (-5), 1]]
def reduceVector : Hol → V
  | DihedralGroup.r k => reduceVectorRot ⟨k.val, ZMod.val_lt k⟩
  | DihedralGroup.sr k => reduceVectorRef ⟨k.val, ZMod.val_lt k⟩

def unit (g : Hol) : V := Pi.single (pivot g) 1
def defect (g : Hol) : Matrix I I ℤ := 1 - pmat ℤ (perm g) * D

theorem ell_unit : ∀ g, ell g ⬝ᵥ unit g = 1 := by decide +kernel
theorem reduction_matrix : ∀ g,
    defect g * reduceMatrix g = 1 - Matrix.vecMulVec (unit g) (ell g) := by decide +kernel
theorem reduction_vector : ∀ g, defect g *ᵥ reduceVector g = (modulus g : ℤ) • unit g := by decide +kernel
theorem ell_defect : ∀ g i, ((ell g ᵥ* defect g) i : ZMod (modulus g)) = 0 := by decide +kernel

end ArtinRinf.Dihedral5
