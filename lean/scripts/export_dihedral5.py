#!/usr/bin/env python3
"""Export exact I₂(5) certificates; Lean checks every emitted identity.

Run from any directory. Requires the pinned SymPy dependency. This exporter
is outside the trusted proof: the generated statements use `decide +kernel`.
"""
import argparse
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--check", action="store_true", help="compare exports without changing files")
args = parser.parse_args()


def emit(relative, text):
    path = ROOT / relative
    if args.check:
        if not path.exists() or path.read_text() != text:
            raise SystemExit(f"Certificate differs: {relative}; rerun this exporter")
    else:
        path.write_text(text)

sys.path.insert(0, str(ROOT / 'code' / 'indep'))
import dihedral_quotient as q
from collections import deque
from pathlib import Path
import sympy as s
sec={q.key(q.I):s.zeros(5,1)};queue=deque([q.I])
while queue:
 g=queue.popleft();a=sec[q.key(g)]
 for b,h in q.generators:
  t=g*h;v=(a+g*b).applyfunc(lambda x:x%2)
  if q.key(t) not in sec:sec[q.key(t)]=v;queue.append(t)
def vec(v):return '!['+', '.join(str(int(x)) if x>=0 else '('+str(int(x))+')' for x in v)+']'
def rows(vs):return '!['+',\n    '.join(vec(v) for v in vs)+']'
text='''/- Exact I₂(5) extension offsets in the manuscript's cyclic coordinates. -/
import ArtinRinf.Aff

namespace ArtinRinf.Dihedral5

abbrev I := Fin 5
abbrev V := I → ℤ
abbrev Hol := DihedralGroup 5

open DihedralGroup

def permFun : Hol → I → I
  | r k, i => ⟨((i.val : ZMod 5) + k).val, ZMod.val_lt _⟩
  | sr k, i => ⟨(-(i.val : ZMod 5) - k).val, ZMod.val_lt _⟩

theorem perm_left : ∀ g i, permFun g⁻¹ (permFun g i) = i := by decide +kernel
theorem perm_right : ∀ g i, permFun g (permFun g⁻¹ i) = i := by decide +kernel

def perm (g : Hol) : Equiv.Perm I := ⟨permFun g, permFun g⁻¹, perm_left g, perm_right g⟩

theorem perm_one : perm 1 = 1 := by decide +kernel
theorem perm_mul : ∀ g h, perm (g * h) = perm g * perm h := by decide +kernel
theorem perm_inv : ∀ g, perm g⁻¹ = (perm g)⁻¹ := by decide +kernel

def rotOffset : Fin 5 → V := ROT

def refOffset : Fin 5 → V := REF

def offset : Hol → V
  | r k => rotOffset ⟨k.val, ZMod.val_lt k⟩
  | sr k => refOffset ⟨k.val, ZMod.val_lt k⟩

theorem offset_one : offset 1 = 0 := by decide +kernel

theorem offset_mul : ∀ g h i,
    (offset (g * h) i : ZMod 2) = (offset g i : ZMod 2) +
      (offset h ((perm g).symm i) : ZMod 2) := by decide +kernel

theorem offset_inv : ∀ g i, (offset g⁻¹ i : ZMod 2) =
    -(offset g (perm g i) : ZMod 2) := by decide +kernel

end ArtinRinf.Dihedral5
'''.replace('ROT',rows([sec[q.key(q.C**k)] for k in range(5)])).replace('REF',rows([sec[q.key(q.S*q.C**k)] for k in range(5)]))
emit('lean/ArtinRinf/Dihedral5/Data.lean', text)

from math import gcd
Gs=[q.C**k for k in range(5)]+[q.S*q.C**k for k in range(5)]
As=[sec[q.key(g)] for g in Gs]
def matrix(M):return rows([list(M.row(i)) for i in range(M.rows)])
def holdef(name,typ,values,render):
 return f'def {name}Rot : Fin 5 → {typ} := !['+',\n    '.join(render(v) for v in values[:5])+']\n'+f'def {name}Ref : Fin 5 → {typ} := !['+',\n    '.join(render(v) for v in values[5:])+']\n'+f'def {name} : Hol → {typ}\n  | DihedralGroup.r k => {name}Rot ⟨k.val, ZMod.val_lt k⟩\n  | DihedralGroup.sr k => {name}Ref ⟨k.val, ZMod.val_lt k⟩\n\n'
M=[q.I-g*q.D for g in Gs];ns=[abs(int(m.det())) for m in M]
ells=[];js=[];Bs=[];us=[]
for m,n in zip(M,ns):
 adj=n*m.inv()
 r,j=next((r,j) for r in range(5) for j in range(5) if gcd(int(adj[r,j]),n)==1)
 ell=(pow(int(adj[r,j]),-1,n)*adj.row(r)).applyfunc(lambda x:x%n)
 B=m.inv()*(q.I-q.E[j]*ell);u=m.inv()*(n*q.E[j])
 assert q.integral(B) and q.integral(u)
 ells.append(ell);js.append(j);Bs.append(B);us.append(u)
corr=[(q.D*a+(q.I-g)*q.d-a)/2 for a,g in zip(As,Gs)]
icorr=[-q.D.inv()*v for v in corr]
assert all(q.integral(c) for c in corr+icorr)
text='''/- Exact arithmetic certificates for I₂(5). Verified by the Lean kernel. -/
import ArtinRinf.Dihedral5.Data
open Matrix
namespace ArtinRinf.Dihedral5

def D : Matrix I I ℤ := DMAT
def Dinv : Matrix I I ℤ := DIMAT
def displacement : V := ![1, 1, 0, 0, 0]

theorem Dinv_D : Dinv * D = 1 := by decide +kernel
theorem D_Dinv : D * Dinv = 1 := by decide +kernel
theorem D_comm : ∀ g, D * pmat ℤ (perm g) = pmat ℤ (perm g) * D := by decide +kernel

'''.replace('DMAT',matrix(q.D)).replace('DIMAT',matrix(q.D.inv()))
text+=holdef('correction','V',corr,vec)+holdef('invCorrection','V',icorr,vec)
text+='''theorem correction_spec : ∀ g,
    D *ᵥ offset g + (displacement - pact (perm g) displacement) =
      offset g + 2 • correction g := by decide +kernel
theorem invCorrection_spec : ∀ g, Dinv *ᵥ correction g + invCorrection g = 0 := by decide +kernel
theorem correction_inv_spec : ∀ g, D *ᵥ invCorrection g + correction g = 0 := by decide +kernel

'''
text+=holdef('modulus','ℕ',ns,str)
text+='''theorem modulus_pos : ∀ g, 0 < modulus g := by decide +kernel
instance modulusNeZero (g : Hol) : NeZero (modulus g) := ⟨Nat.ne_of_gt (modulus_pos g)⟩
instance modulusFintype (g : Hol) : Fintype (ZMod (modulus g)) := inferInstance

'''
text+=holdef('ell','V',ells,vec)+holdef('pivot','I',js,str)+holdef('reduceMatrix','Matrix I I ℤ',Bs,matrix)+holdef('reduceVector','V',us,vec)
text+='''def unit (g : Hol) : V := Pi.single (pivot g) 1
def defect (g : Hol) : Matrix I I ℤ := 1 - pmat ℤ (perm g) * D

theorem ell_unit : ∀ g, ell g ⬝ᵥ unit g = 1 := by decide +kernel
theorem reduction_matrix : ∀ g,
    defect g * reduceMatrix g = 1 - Matrix.vecMulVec (unit g) (ell g) := by decide +kernel
theorem reduction_vector : ∀ g, defect g *ᵥ reduceVector g = (modulus g : ℤ) • unit g := by decide +kernel
theorem ell_defect : ∀ g i, ((ell g ᵥ* defect g) i : ZMod (modulus g)) = 0 := by decide +kernel

end ArtinRinf.Dihedral5
'''
emit('lean/ArtinRinf/Dihedral5/Matrices.lean', text)

# Gs, As, M, ns, ells, js etc are reconstructed exactly.
target=[[Gs.index(h*g*h.T) for h in Gs] for g in Gs]
shift=[[None]*10 for _ in Gs];slope=[[0]*10 for _ in Gs];inter=[[0]*10 for _ in Gs]
for i,g in enumerate(Gs):
 for j,h in enumerate(Gs):
  k=target[i][j]
  v=(As[j]+h*As[i]-Gs[k]*(q.D*As[j]+(q.I-h)*q.d)-As[k])/2
  assert q.integral(v)
  shift[i][j]=v
  slope[i][j]=int((ells[k]*h*q.E[js[i]])[0])%ns[k]
  inter[i][j]=int((ells[k]*v)[0])%ns[k]
  assert all(int(v)%ns[k]==0 for v in ells[k]*h-slope[i][j]*ells[i])
def move(h,state):
 i,k=state;return target[i][h],(slope[i][h]*k+inter[i][h])%ns[i]
states=[(i,k) for i,n in enumerate(ns) for k in range(n)]
labels={};reps=[];witness={}
for state in states:
 if state in labels:continue
 orbit={move(h,state) for h in range(10)}
 idx=len(reps);reps.append(state)
 for s0 in orbit:
  labels[s0]=idx
  witness[s0]=next(h for h in range(10) if move(h,s0)==state)
assert len(reps)==18

def table(name,typ,data,render):
 return f'def {name}Table : Fin 10 → Fin 10 → {typ} := !['+',\n'.join('!['+', '.join(render(v) for v in row)+']' for row in data)+']\n'+f'def {name} (g h : Hol) : {typ} := {name}Table (holIndex g) (holIndex h)\n\n'
text='''/- Finite affine action on all 140 translation-twisted classes. -/
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

'''
text+=table('twistOffset','V',shift,vec)+table('slope','ℤ',slope,str)+table('intercept','ℤ',inter,str)
text+='''theorem twistOffset_spec : ∀ g h,
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

'''
text+='def labelTable : Fin 10 → Fin 22 → Fin 18 := !['+',\n'.join('!['+', '.join(str(labels.get((i,k),0)) for k in range(22))+']' for i in range(10))+']\n'
text+='''def label (s : State) : Fin 18 := labelTable (holIndex s.1) (Fin.ofNat 22 s.2.val)

'''
text+='def representative : Fin 18 → State := !['+', '.join(f'⟨holAt {g}, {k}⟩' for g,k in reps)+']\n'
text+='def conjugatorTable : Fin 10 → Fin 22 → Fin 10 := !['+',\n'.join('!['+', '.join(str(witness.get((i,k),0)) for k in range(22))+']' for i in range(10))+']\n'
text+='''def conjugator (s : State) : Hol := holAt (conjugatorTable (holIndex s.1) (Fin.ofNat 22 s.2.val))

theorem label_move : ∀ h s, label (move h s) = label s := by decide +kernel
theorem move_representative : ∀ s, move (conjugator s) s = representative (label s) := by decide +kernel
theorem label_representative : ∀ i, label (representative i) = i := by decide +kernel
theorem state_card : Fintype.card State = 140 := by decide +kernel

end ArtinRinf.Dihedral5
'''
emit('lean/ArtinRinf/Dihedral5/ActionData.lean', text)

print("ALL CHECKS PASSED: three exact I₂(5) certificates")
