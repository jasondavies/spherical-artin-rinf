/- Finite affine action on all 140 translation-twisted classes. -/
import ArtinRinf.Dihedral5.Matrices
open Matrix DihedralGroup
namespace ArtinRinf.Dihedral5

def holIndex : Hol → Fin 10
  | r k => Fin.ofNat 10 k.val
  | sr k => Fin.ofNat 10 (5 + k.val)

def holAt (i : Fin 10) : Hol :=
  if i.val < 5 then r (i.val : ZMod 5) else sr ((i.val - 5 : ℕ) : ZMod 5)

theorem holAt_index : ∀ g, holAt (holIndex g) = g := by decide +kernel

def conjugate (g h : Hol) : Hol := h * g * h⁻¹

theorem modulus_conjugate : ∀ g h, modulus (conjugate g h) = modulus g := by decide +kernel

def twistOffsetTable : Fin 10 → Fin 10 → V := ![![![0, 0, 0, 0, 0], ![0, 1, 1, 1, 1], ![0, 0, 1, 1, 0], ![0, 0, 0, 1, 1], ![1, 0, 1, 1, 1], ![0, 0, 0, 0, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 1, 1], ![0, 0, 1, 0, 0], ![1, 1, 1, 1, 1]],
![![0, 0, 0, 0, 0], ![1, 0, 1, 1, 1], ![0, 1, 0, 0, 1], ![1, 0, 0, 0, 1], ![0, 2, 0, 1, 1], ![1, 0, 0, 1, (-1)], ![0, 1, 1, 1, 0], ![1, 1, 0, 1, 0], ![0, 1, 0, 0, 0], ![1, 1, 1, 1, 1]],
![![0, 0, 0, 0, 0], ![1, 0, 0, 2, 1], ![1, 0, 0, 0, 1], ![2, 0, (-1), 0, 1], ![1, 1, 1, 0, 1], ![0, 0, 1, 0, 0], ![0, 1, 2, 1, (-1)], ![1, 1, 1, 0, 0], ![1, 1, 0, 0, (-1)], ![1, 1, 1, 1, 1]],
![![0, 0, 0, 0, 0], ![1, 1, 1, 0, 1], ![0, 2, 1, 0, (-1)], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![1, 1, (-1), 0, 0], ![1, 1, 0, 0, 1], ![1, 0, (-1), 1, 2], ![0, 0, 0, 0, 1], ![1, 1, 1, 1, 1]],
![![0, 0, 0, 0, 0], ![2, 0, 1, 1, 0], ![0, 1, 1, 0, 0], ![1, 0, 1, 0, 0], ![0, 1, 1, 1, 1], ![1, 0, 0, 0, 0], ![1, 1, 0, 1, 0], ![1, 0, 0, 1, 1], ![0, 1, (-1), 1, 0], ![1, 1, 1, 1, 1]],
![![0, 0, 0, 0, 0], ![1, 1, 0, 1, 1], ![0, 1, 1, (-1), 0], ![0, (-1), 0, 1, 0], ![0, 1, 0, 1, 1], ![0, 1, 0, 0, 0], ![0, 1, 0, 0, 1], ![0, (-1), 0, 1, 1], ![0, 0, 1, (-1), 0], ![1, 1, 1, 1, 1]],
![![0, 0, 0, 0, 0], ![1, (-1), 1, 1, 1], ![1, 1, 0, 0, 0], ![0, 1, 1, 0, 1], ![1, 0, 2, 1, 1], ![0, (-1), 1, 0, 0], ![1, 1, 1, 0, 0], ![2, 0, 0, 1, 1], ![0, 1, 0, 1, 0], ![1, 1, 1, 1, 1]],
![![0, 0, 0, 0, 0], ![0, 1, 1, 1, 2], ![1, 0, 1, 0, 1], ![1, 1, 0, 0, 0], ![(-1), 1, 1, 1, 1], ![1, 0, 0, 1, 0], ![0, 2, 1, 1, 0], ![1, 1, 0, 0, 1], ![(-1), 0, 0, 0, 1], ![1, 1, 1, 1, 1]],
![![0, 0, 0, 0, 0], ![1, 0, 1, 1, 0], ![(-1), 0, 0, 1, 0], ![1, 0, 0, (-1), 1], ![1, 1, 1, 1, 0], ![0, 0, 0, (-1), 1], ![(-1), 0, 1, 1, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 0, 0], ![1, 1, 1, 1, 1]],
![![0, 0, 0, 0, 0], ![1, 1, 2, 0, 1], ![0, 1, 2, 1, 0], ![1, 0, 0, 1, 2], ![1, 1, 1, 0, 2], ![2, 0, 0, 0, 0], ![1, 0, 1, 2, 1], ![0, 1, 1, 2, 1], ![0, 2, 0, 0, 0], ![1, 1, 1, 1, 1]]]
def twistOffset (g h : Hol) : V := twistOffsetTable (holIndex g) (holIndex h)

def slopeTable : Fin 10 → Fin 10 → ℤ := ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
![1, 5, 3, 15, 9, 1, 5, 3, 15, 9],
![1, 3, 9, 5, 15, 1, 3, 9, 5, 15],
![1, 15, 5, 9, 3, 1, 15, 5, 9, 3],
![1, 9, 15, 3, 5, 1, 9, 15, 3, 5],
![1, 9, 7, 3, 1, 9, 9, 7, 3, 1],
![1, 9, 3, 3, 7, 1, 9, 3, 7, 7],
![1, 1, 9, 7, 3, 1, 9, 9, 7, 3],
![1, 3, 7, 9, 9, 1, 3, 7, 9, 1],
![1, 7, 7, 3, 9, 1, 7, 3, 3, 9]]
def slope (g h : Hol) : ℤ := slopeTable (holIndex g) (holIndex h)

def interceptTable : Fin 10 → Fin 10 → ℤ := ![![0, 0, 0, 0, 0, 1, 1, 1, 1, 1],
![0, 6, 14, 10, 12, 21, 5, 13, 9, 11],
![0, 4, 16, 8, 6, 5, 9, 21, 13, 11],
![0, 2, 10, 20, 16, 17, 19, 5, 15, 11],
![0, 20, 2, 16, 10, 1, 21, 3, 17, 11],
![0, 6, 1, 6, 1, 1, 2, 9, 8, 5],
![0, 7, 8, 7, 9, 8, 9, 2, 4, 5],
![0, 9, 7, 4, 3, 4, 2, 3, 2, 5],
![0, 3, 4, 7, 6, 6, 1, 6, 1, 5],
![0, 9, 8, 8, 7, 2, 3, 3, 4, 5]]
def intercept (g h : Hol) : ℤ := interceptTable (holIndex g) (holIndex h)

theorem twistOffset_spec : ∀ g h,
    offset h + pact (perm h) (offset g) -
      pact (perm (conjugate g h)) (D *ᵥ offset h + (displacement - pact (perm h) displacement)) =
    offset (conjugate g h) + 2 • twistOffset g h := by decide +kernel

theorem ell_transport : ∀ g h i,
    ((ell (conjugate g h) ᵥ* pmat ℤ (perm h)) i : ZMod (modulus (conjugate g h))) =
      ((slope g h * ell g i : ℤ) : ZMod (modulus (conjugate g h))) := by decide +kernel

theorem ell_shift : ∀ g h,
    ((ell (conjugate g h) ⬝ᵥ twistOffset g h : ℤ) : ZMod (modulus (conjugate g h))) =
      (intercept g h : ZMod (modulus (conjugate g h))) := by decide +kernel

abbrev State := (g : Hol) × ZMod (modulus g)

def move (h : Hol) (s : State) : State :=
  ⟨conjugate s.1 h, ((slope s.1 h * (s.2.val : ℤ) + intercept s.1 h : ℤ) : ZMod _)⟩

def labelTable : Fin 10 → Fin 22 → Fin 18 := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![1, 2, 3, 2, 4, 5, 1, 5, 3, 5, 1, 2, 1, 5, 1, 6, 3, 2, 3, 5, 3, 2],
![7, 8, 9, 8, 7, 10, 7, 8, 7, 11, 9, 10, 9, 8, 9, 10, 7, 10, 9, 10, 12, 8],
![10, 9, 10, 12, 8, 7, 8, 9, 8, 7, 10, 7, 8, 7, 11, 9, 10, 9, 8, 9, 10, 7],
![2, 3, 2, 4, 5, 1, 5, 3, 5, 1, 2, 1, 5, 1, 6, 3, 2, 3, 5, 3, 2, 1],
![13, 13, 14, 15, 16, 17, 17, 16, 15, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![16, 13, 15, 17, 14, 14, 17, 15, 13, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![14, 13, 13, 14, 15, 16, 17, 17, 16, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![17, 17, 16, 15, 14, 13, 13, 14, 15, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![15, 17, 14, 14, 17, 15, 13, 16, 16, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def label (s : State) : Fin 18 := labelTable (holIndex s.1) (Fin.ofNat 22 s.2.val)

def representative : Fin 18 → State := ![⟨holAt 0, 0⟩, ⟨holAt 1, 0⟩, ⟨holAt 1, 1⟩, ⟨holAt 1, 2⟩, ⟨holAt 1, 4⟩, ⟨holAt 1, 5⟩, ⟨holAt 1, 15⟩, ⟨holAt 2, 0⟩, ⟨holAt 2, 1⟩, ⟨holAt 2, 2⟩, ⟨holAt 2, 5⟩, ⟨holAt 2, 9⟩, ⟨holAt 2, 20⟩, ⟨holAt 5, 0⟩, ⟨holAt 5, 2⟩, ⟨holAt 5, 3⟩, ⟨holAt 5, 4⟩, ⟨holAt 5, 5⟩]
def conjugatorTable : Fin 10 → Fin 22 → Fin 10 := ![![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![0, 0, 0, 2, 0, 0, 4, 3, 1, 4, 2, 4, 1, 1, 3, 0, 4, 3, 2, 2, 3, 1],
![0, 0, 0, 3, 4, 0, 1, 4, 2, 0, 4, 2, 3, 2, 1, 1, 3, 3, 2, 4, 0, 1],
![7, 8, 6, 5, 9, 5, 5, 5, 7, 6, 5, 9, 6, 8, 5, 6, 8, 7, 8, 9, 9, 7],
![5, 5, 8, 5, 5, 6, 7, 9, 6, 8, 6, 9, 9, 7, 5, 6, 7, 8, 8, 7, 9, 5],
![0, 5, 0, 0, 0, 0, 5, 5, 5, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![8, 3, 3, 8, 8, 3, 3, 8, 8, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![6, 1, 6, 1, 1, 1, 1, 6, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![9, 4, 4, 4, 4, 9, 4, 9, 9, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
![7, 2, 2, 7, 7, 2, 2, 7, 2, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def conjugator (s : State) : Hol := holAt (conjugatorTable (holIndex s.1) (Fin.ofNat 22 s.2.val))

theorem label_move : ∀ h s, label (move h s) = label s := by decide +kernel
theorem move_representative : ∀ s, move (conjugator s) s = representative (label s) := by decide +kernel
theorem label_representative : ∀ i, label (representative i) = i := by decide +kernel
theorem state_card : Fintype.card State = 140 := by decide +kernel

end ArtinRinf.Dihedral5
