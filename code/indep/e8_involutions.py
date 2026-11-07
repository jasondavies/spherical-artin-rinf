#!/usr/bin/env python3
"""Referee's check: all involution classes of G = W(E8)/{+-1}, acting on the 120 root lines.

Involutions of G lift to w in W with w^2 = 1 or w^2 = -1.
 * w^2 = 1: w is a product of reflections in k mutually orthogonal roots (Carter 1972, Lemma 5;
   or Steinberg's fixed-point theorem), and w, -w have the same image, so k <= 4 suffices.
   We enumerate ALL orthogonal k-frames of root lines, k = 1..4, form the products, and split
   into G-conjugacy classes by BFS.
 * w^2 = -1: exhibited explicitly (signed permutation in W(D8)); by Springer's theory of regular
   elements (i is a regular eigenvalue for E8, eigenspace dim a(4)=4) these form one W-class.
Also checks which classes lie in [G,G] (image of the rotation subgroup W^+), using det of a lift.
"""
import itertools, sys
import numpy as np

# E8 roots in doubled coordinates
roots = []
for i, j in itertools.combinations(range(8), 2):
    for si in (2, -2):
        for sj in (2, -2):
            v = [0]*8; v[i] = si; v[j] = sj; roots.append(tuple(v))
for signs in itertools.product((1, -1), repeat=8):
    if signs.count(-1) % 2 == 0: roots.append(signs)
assert len(roots) == 240
R = np.array(roots, dtype=np.int64)
gram = R @ R.T   # doubled^2 : equals 4*(a,b)
assert set(np.unique(gram)) <= {-8, -4, 0, 4, 8}
# lines: pick the representative with first nonzero coordinate positive
lines = [k for k, v in enumerate(roots) if next(x for x in v if x != 0) > 0]
assert len(lines) == 120
lidx = {}
for li, k in enumerate(lines):
    lidx[roots[k]] = li; lidx[tuple(-x for x in roots[k])] = li
L = R[lines]                     # 120 x 8
def refl_matrix(b):
    return np.array(b, dtype=np.int64)
def perm_of_refl(b):
    # s_b(x) = x - (<x,b>_d / 4) b  in doubled coords (norm_d = 8); <x,b>_d in 4Z for roots x
    ip = L @ b
    assert (ip % 4 == 0).all()
    img = L - np.outer(ip // 4, b)
    return np.array([lidx[tuple(int(t) for t in r)] for r in img], dtype=np.int64)
def perm_of_matrix(Mx):
    if Mx.ndim == 1: return perm_of_refl(Mx)
    img = L @ Mx.T
    return np.array([lidx[tuple(int(t) for t in r)] for r in img], dtype=np.int64)

# simple roots (Bourbaki), doubled
simple = [(1,-1,-1,-1,-1,-1,-1,1), (2,2,0,0,0,0,0,0)] + \
         [tuple(-2 if t == k-1 else (2 if t == k else 0) for t in range(8)) for k in range(1, 7)]
for s in simple: assert s in lidx
gens = [perm_of_matrix(refl_matrix(s)) for s in simple]
refl_perm = [perm_of_matrix(refl_matrix(L[i])) for i in range(120)]
assert len({p.tobytes() for p in refl_perm}) == 120

def conj_class(x, cap=None):
    seen = {x.tobytes()}; fr = [x]
    while fr:
        nf = []
        for y in fr:
            for s in gens:
                z = s[y[s]]           # s y s  (s an involution): (s*y*s)(i) = s[y[s[i]]]
                kb = z.tobytes()
                if kb not in seen:
                    seen.add(kb); nf.append(z)
                    if cap and len(seen) > cap: return seen
        fr = nf
    return seen

G2 = (gram[np.ix_(lines, lines)] == 0)  # orthogonality of lines
# enumerate orthogonal frames
frames = {1: [(i,) for i in range(120)]}
for k in range(2, 5):
    nxt = []
    for f in frames[k-1]:
        for j in range(f[-1]+1, 120):
            if all(G2[i, j] for i in f): nxt.append(f + (j,))
    frames[k] = nxt
print("orthogonal k-frames of root lines:", {k: len(v) for k, v in frames.items()})

def det_lift_sign(k):  # det of product of k reflections
    return (-1)**k

allinv = {}   # perm bytes -> k
for k in range(1, 5):
    for f in frames[k]:
        p = np.arange(120)
        for i in f: p = refl_perm[i][p]
        allinv.setdefault(p.tobytes(), k)
print("distinct involutions of G with lift w^2=1 (from k<=4 frames):", len(allinv),
      " by k:", {k: sum(1 for v in allinv.values() if v == k) for k in range(1, 5)})
# split into classes
remaining = set(allinv)
classes = []
while remaining:
    b = next(iter(remaining))
    x = np.frombuffer(b, dtype=np.int64).copy()
    cl = conj_class(x)
    assert cl <= set(allinv)
    remaining -= cl
    nfix = int((x == np.arange(120)).sum())
    classes.append((len(cl), allinv[b], nfix))
classes.sort()
print("classes of involutions with w^2=1: (size, k, #fixed lines):", classes)

# w^2 = -1 element: (x1,x2)->(-x2,x1) on 4 coordinate pairs, an even signed permutation, in W(D8) < W(E8)
J = np.zeros((8, 8), dtype=np.int64)
for a in range(0, 8, 2):
    J[a+1, a] = 1; J[a, a+1] = -1
assert (J @ J == -np.eye(8, dtype=np.int64)).all()
pJ = perm_of_matrix(J)
assert (pJ[pJ] == np.arange(120)).all()
clJ = conj_class(pJ)
print("class of the w^2=-1 involution: size", len(clJ), ", fixed lines", int((pJ == np.arange(120)).sum()),
      ", disjoint from w^2=1 involutions:", not (clJ & set(allinv)))
print("sizes equal to 120:", [c for c in classes if c[0] == 120], "+ (w^2=-1 class)" if len(clJ) == 120 else "")
print("|G| / class size = centralizer orders:", [(348364800 // c[0], c[1]) for c in classes], 348364800 // len(clJ))
# group order via sympy (independent of the package's Schreier-Sims)
try:
    from sympy.combinatorics import Permutation, PermutationGroup
    PG = PermutationGroup([Permutation(list(map(int, g))) for g in gens])
    print("|G| (sympy Schreier-Sims):", PG.order())
except Exception as ex:
    print("sympy failed:", ex)
