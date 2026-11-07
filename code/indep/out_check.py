"""Independent computation of |Out(rho(W))|, rho(W) = W/Z(W) acting on the reflections R.

Fresh code (does not use fastaut.py / pgrp.py).  Two steps:

 (1) Enumerate rho(W), its involutions and their conjugacy classes.  Check that no involution class
     other than the reflection classes has the size of a reflection class.  Hence every automorphism
     of rho(W) maps the set of reflections rho(R) onto itself.  (We also check that r -> rho(r) is
     injective on R, so reflections can be identified with points of the permutation domain and
     centralisers of reflections with point stabilisers.)

 (2) Count Inn(rho(W))-orbits of "Coxeter tuples" (t_1..t_n) of reflections with
         ord(t_i t_j) = ord(rho(s_i) rho(s_j))   for all i<j,   and   <t_1..t_n> = rho(W).
     Each such tuple defines a surjection W -> rho(W) whose kernel has order |Z(W)| <= 2, hence is
     Z(W); so tuples <-> automorphisms mapping each rho(s_i) into rho(R), i.e. (by (1)) all of
     Aut(rho(W)).  Since Z(rho(W)) = 1, Inn acts freely, and the number of orbits is |Out(rho(W))|.
     Orbits are enumerated by the standard stabiliser-chain search (orbit representatives at each level).
"""
import sys, time
import numpy as np
from rootsys import RootSystem
from permgroup import enumerate_group, centre, order, generated_order

def run(name):
    t0 = time.time()
    rs = RootSystem(name); N = rs.N; n = rs.n
    E, index = enumerate_group(rs.gens)
    dt = E.dtype; G = len(E)
    print(f'===== {name}: |rho(W)| = {G}, |R| = {N}', flush=True)
    print(f'  centre of rho(W): order {len(centre(E, rs.gens))}', flush=True)
    # reflections as group elements
    refl = [np.array(rs.perm_of(rs.R[r]), dtype=dt) for r in range(N)]
    refl_idx = [index[p.tobytes()] for p in refl]
    print(f'  r -> rho(r) injective on R: {len(set(refl_idx)) == N}', flush=True)
    # (1) involutions and their classes
    ar = np.arange(N, dtype=dt)
    inv_idx = []
    for k in range(0, G, 200000):
        X = E[k:k + 200000]
        sq = np.take_along_axis(X, X.astype(np.int64), axis=1)
        inv_idx.extend((k + np.where(np.all(sq == ar, axis=1) & ~np.all(X == ar, axis=1))[0]).tolist())
    loc = {g: i for i, g in enumerate(inv_idx)}
    parent = list(range(len(inv_idx)))
    def find(a):
        while parent[a] != a: parent[a] = parent[parent[a]]; a = parent[a]
        return a
    X = E[inv_idx]
    for g in rs.gens:
        g = np.asarray(g, dtype=dt)
        Y = g[X[:, g]]                     # g o x o g^{-1}  (g is an involution)
        for i, row in enumerate(Y):
            j = loc[index[row.tobytes()]]
            a, b = find(i), find(j)
            if a != b: parent[a] = b
    roots = {}
    for i in range(len(inv_idx)): roots.setdefault(find(i), []).append(i)
    classes = list(roots.values())
    sizes = sorted(len(c) for c in classes)
    refl_classes = {find(loc[g]) for g in refl_idx}
    refl_sizes = sorted({len(roots[c]) for c in refl_classes})
    others_same_size = [len(roots[c]) for c in roots if c not in refl_classes and len(roots[c]) in refl_sizes]
    print(f'  {len(inv_idx)} involutions in {len(classes)} classes, sizes {sizes}', flush=True)
    print(f'  reflection classes: {len(refl_classes)} of sizes {[len(roots[c]) for c in refl_classes]}; '
          f'other involution classes of a reflection-class size: {others_same_size} '
          f'-> automorphisms preserve rho(R): {not others_same_size}', flush=True)
    # (2) orbit search on Coxeter tuples
    ordtab = np.zeros((N, N), int)
    for a in range(N):
        for b in range(N):
            ordtab[a, b] = order(refl[a][refl[b]]) if a != b else 1
    target = [[ordtab[rs.sidx[i], rs.sidx[j]] for j in range(n)] for i in range(n)]
    leaves = []; nodes = [0]
    def search(tup, H):
        nodes[0] += 1
        k = len(tup)
        if k == n:
            if generated_order([refl[t] for t in tup]) == G: leaves.append(tuple(tup))
            return
        cand = [c for c in range(N) if all(ordtab[tup[j], c] == target[j][k] for j in range(k))]
        done = set()
        for c in cand:
            if c in done: continue
            orb = set(E[H, c].tolist()); done |= orb
            search(tup + [c], H[E[H, c] == c])
    allidx = np.arange(G)
    done0 = set()
    for r in range(N):                     # level 0: representatives of rho(W)-orbits on R
        if r in done0: continue
        done0 |= set(E[:, r].tolist())
        search([r], allidx[E[:, r] == r])
    std = tuple(rs.sidx)
    print(f'  search nodes {nodes[0]}; Inn-orbits of generating Coxeter tuples of reflections: {len(leaves)}  => |Out(rho(W))| = {len(leaves)}',
          flush=True)
    print(f'  [{name} done in {time.time() - t0:.1f}s]', flush=True)
    exp = {'H3': 2, 'H4': 2, 'F4': 2, 'D5': 1, 'E6': 1, 'E7': 1}
    if name in exp and (len(leaves) != exp[name] or others_same_size or len(set(refl_idx)) != N):
        FAIL.append(name)

FAIL = []
if __name__ == '__main__':
    if not sys.argv[1:]:
        sys.exit('Usage: out_check.py TYPE [TYPE ...]')
    for nm in sys.argv[1:]: run(nm)
    if FAIL: print('FAILED CHECKS:', FAIL); sys.exit(1)
    print('ALL CHECKS PASSED')
