"""Partial check for groups too large to enumerate (E8): step (2) of out_check.py only,
using Schreier-Sims stabiliser chains (sympy) instead of element lists.

Proves: every automorphism of rho(W) that maps the set of reflections rho(R) onto itself is inner
(number of Inn-orbits of generating Coxeter tuples of reflections = 1).
Does NOT prove that every automorphism of rho(W) preserves rho(R) (step (1)); the paper proves
that step for E8 using its involutions and the pointwise-stabiliser theorem.
"""
import sys, time
import numpy as np
from sympy.combinatorics import Permutation, PermutationGroup
from rootsys import RootSystem
from permgroup import order

def run(name):
    t0 = time.time()
    rs = RootSystem(name); N = rs.N; n = rs.n
    G = PermutationGroup([Permutation(list(g)) for g in rs.gens])
    oG = G.order()
    print(f'===== {name}: |rho(W)| = {oG} (Schreier-Sims), |R| = {N}', flush=True)
    refl = [np.array(rs.perm_of(rs.R[r])) for r in range(N)]
    print(f'  r -> rho(r) injective on R: {len({p.tobytes() for p in refl}) == N}', flush=True)
    ordtab = np.ones((N, N), int)
    for a in range(N):
        for b in range(N):
            if a != b: ordtab[a, b] = order(refl[a][refl[b]])
    target = [[ordtab[rs.sidx[i], rs.sidx[j]] for j in range(n)] for i in range(n)]
    leaves = []; nodes = [0]
    def search(tup, H):
        nodes[0] += 1; k = len(tup)
        if k == n:
            sub = PermutationGroup([Permutation([int(x) for x in refl[t]]) for t in tup])
            if sub.order() == oG: leaves.append(tuple(tup))
            return
        cand = [c for c in range(N) if all(ordtab[tup[j], c] == target[j][k] for j in range(k))]
        done = set()
        for c in cand:
            if c in done: continue
            done |= set(H.orbit(c))
            search(tup + [c], H.stabilizer(c))
    done0 = set()
    for r in range(N):
        if r in done0: continue
        done0 |= set(G.orbit(r))
        search([r], G.stabilizer(r))
    print(f'  search nodes {nodes[0]}; Inn-orbits of generating Coxeter tuples of reflections: {len(leaves)}', flush=True)
    print(f'  => every automorphism of rho(W) preserving rho(R) is inner: {len(leaves) == 1}', flush=True)
    if len(leaves) != 1: FAIL.append(name)
    print(f'  [{name} done in {time.time() - t0:.1f}s]', flush=True)

FAIL = []
if __name__ == '__main__':
    if not sys.argv[1:]:
        sys.exit('Usage: out_check_stab.py TYPE [TYPE ...]')
    for nm in sys.argv[1:]: run(nm)
    if FAIL: print('FAILED CHECKS:', FAIL); sys.exit(1)
    print('ALL CHECKS PASSED')
