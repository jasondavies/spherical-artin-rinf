"""Exploratory check: does the criterion (Theorem 3.1, weakened hypothesis) apply to the classical types?

For a type (A_n, B_n, D_n, I2(m), or any exceptional type):
  1. enumerate G = rho(W) acting on the reflections R;
  2. involution classes, their sizes and permutation-character values chi_R.  An automorphism theta induced by
     Aut(A) satisfies chi_R o theta = chi_R (trace of M_phi rho(w) M_phi^{-1}).  If every involution class with the
     size and chi_R-value of a reflection class is itself a reflection class, then every such theta preserves rho(R);
  3. Inn-orbits of reflection-preserving automorphisms (generating Coxeter tuples of reflections);
  4. good constituents (exact eigenspaces of a random commutant element, certified by characters);
  5. for each automorphism class: the permutation pi, and conditions (i)/(ii) of Theorem 3.1 checked exactly.
This is a finite check for the listed ranks only.
"""
import sys, time
import numpy as np
from fractions import Fraction as Fr
from rootsys import RootSystem
from permgroup import enumerate_group, centre, order, inverse, generated_order
from indep_check import nullspace_basis, int_basis, character, nullity, permmat

class Dihedral:
    """I2(m): reflections r_k = rho^k s (k mod m); r_k r_j r_k = r_{2k-j}; s = r_0, t = r_{m-1}."""
    def __init__(self, m):
        self.N = m; self.n = 2; self.name = f'I2({m})'
        self.refl = [tuple((2 * k - j) % m for j in range(m)) for k in range(m)]
        self.sidx = [0, m - 1]
        self.gens = [self.refl[0], self.refl[m - 1]]
        self.coxeter = [[1, m], [m, 1]]

def make(name):
    if name.startswith('I2('):
        return Dihedral(int(name[3:-1]))
    rs = RootSystem(name)
    rs.refl = [rs.perm_of(rs.R[r]) for r in range(rs.N)]
    return rs

def analyze(name, verbose=True):
    t0 = time.time()
    rs = make(name); N, n = rs.N, rs.n
    E, index = enumerate_group(rs.gens); G = len(E); dt = E.dtype
    refl = [np.array(p, dtype=dt) for p in rs.refl]
    refl_idx = [index[p.tobytes()] for p in refl]
    inj = len(set(refl_idx)) == N
    fix = (E == np.arange(N, dtype=dt)).sum(axis=1)
    # involution classes
    sq = np.take_along_axis(E, E.astype(np.int64), axis=1)
    inv = np.where(np.all(sq == np.arange(N, dtype=dt), axis=1) & ~np.all(E == np.arange(N, dtype=dt), axis=1))[0]
    loc = {g: i for i, g in enumerate(inv.tolist())}
    par = list(range(len(inv)))
    def find(a):
        while par[a] != a: par[a] = par[par[a]]; a = par[a]
        return a
    X = E[inv]
    for g in rs.gens:
        g = np.asarray(g, dtype=dt); Y = g[X[:, g]]
        for i, row in enumerate(Y):
            a, b = find(i), find(loc[index[row.tobytes()]])
            if a != b: par[a] = b
    cls = {}
    for i in range(len(inv)): cls.setdefault(find(i), []).append(int(inv[i]))
    rcl = {find(loc[g]) for g in refl_idx}
    sig = lambda c: (len(cls[c]), int(fix[cls[c][0]]))
    rsig = {sig(c) for c in rcl}
    clash = [sig(c) for c in cls if c not in rcl and sig(c) in rsig]
    # orbit search: reflection-preserving automorphisms up to Inn
    ordtab = np.ones((N, N), int)
    for a in range(N):
        for b in range(N):
            if a != b: ordtab[a, b] = order(refl[a][refl[b]])
    target = [[ordtab[rs.sidx[i], rs.sidx[j]] for j in range(n)] for i in range(n)]
    leaves = []
    def search(tup, H):
        k = len(tup)
        if k == n:
            if generated_order([refl[t] for t in tup]) == G: leaves.append(tuple(tup))
            return
        cand = [c for c in range(N) if all(ordtab[tup[j], c] == target[j][k] for j in range(k))]
        done = set()
        for c in cand:
            if c in done: continue
            done |= set(E[H, c].tolist())
            search(tup + [c], H[E[H, c] == c])
    seen0 = set(); allidx = np.arange(G)
    for r in range(N):
        if r in seen0: continue
        seen0 |= set(E[:, r].tolist())
        search([r], allidx[E[:, r] == r])
    # good constituents: eigenspaces of a random symmetric commutant element (orbital matrices)
    lab = -np.ones((N, N), int); k = 0
    for a in range(N):
        for b in range(N):
            if lab[a, b] < 0:
                st = [(a, b)]; lab[a, b] = k
                while st:
                    x, y = st.pop()
                    for g in rs.gens:
                        u, v = g[x], g[y]
                        if lab[u, v] < 0: lab[u, v] = k; st.append((u, v))
                k += 1
    rng = np.random.default_rng(11); c = rng.integers(1, 100, size=k)
    Xc = np.zeros((N, N), dtype=np.int64)
    for i in range(k): Xc += int(c[i]) * (lab == i)
    Xc = Xc + Xc.T
    ev = np.linalg.eigvalsh(Xc.astype(float))
    good = []; others = []
    for lam in sorted(set(int(round(x)) for x in ev if abs(x - round(x)) < 1e-6)):
        B = nullspace_basis(Xc - lam * np.eye(N, dtype=np.int64))
        if B.shape[1] == 0: continue
        Bi = int_basis(B); chi = character(Bi, E); d = Bi.shape[1]
        n1 = Fr(int((chi * chi).sum()), G); n2 = Fr(int((chi * fix.astype(np.int64)).sum()), G)
        moved = [i for i in range(n) if chi[index[np.asarray(rs.gens[i], dtype=dt).tobytes()]] != d]
        if n1 == 1 and n2 == 1 and d >= 1 and moved: good.append((d, Bi, moved))
        else: others.append((d, n1, n2))
    # criterion per automorphism class
    std = tuple(rs.sidx)
    results = []
    for leaf in leaves:
        # pi with pi(s_i) = t_i and pi rho(s_i) pi^{-1} = rho(t_i): BFS over R
        pi = -np.ones(N, int)
        for i in range(n): pi[rs.sidx[i]] = leaf[i]
        st = list(rs.sidx); ok = True
        while st:
            r = st.pop()
            for i in range(n):
                r2 = rs.gens[i][r]; img = refl[leaf[i]][pi[r]]
                if pi[r2] < 0: pi[r2] = img; st.append(r2)
                elif pi[r2] != img: ok = False
        ok = ok and len(set(pi.tolist())) == N
        pi = pi.astype(dt); pinv = inverse(pi)
        ok = ok and all(np.array_equal(pi[np.asarray(g, dtype=dt)][pinv], refl[t]) for g, t in zip(rs.gens, leaf))
        verdict = None
        # images of good constituents
        Pp = permmat(pi)
        def proj_eq(Ba, Bb):
            from indep_check import dm
            return dm(np.hstack([Bb, Pp @ Ba]).T.tolist()).rank() == Bb.shape[1]   # exact
        for a, (d, Ba, _) in enumerate(good):
            Q, _ = np.linalg.qr(Ba.astype(float))
            img = [b for b, (db, Bb, _) in enumerate(good) if db == d and proj_eq(Ba, Bb)]
            stable = img == [a]
            found = {}
            for eps in (1, -1):
                for x in range(G):
                    q = E[x][pi]
                    if not stable: q = q[q]
                    qinv = inverse(q)
                    M = Q.T @ Q[qinv]
                    if np.min(np.abs(np.linalg.eigvals(M) - eps)) < 1e-6:
                        if nullity((permmat(q) - eps * np.eye(N, dtype=np.int64)) @ Ba) > 0:
                            found[eps] = x; break
            if len(found) == 2 and (stable or (len(img) == 1 and img[0] != a)):
                verdict = ('(i)' if stable else '(ii)', d); break
        results.append((leaf == std, ok, verdict))
    dims_good = [d for d, _, _ in good]
    out = dict(name=name, G=G, N=N, inj=inj, clash=clash, nout=len(leaves), good=dims_good, others=others,
               results=results, t=time.time() - t0)
    if verbose:
        print(f'===== {name}: |rho(W)| = {G}, |R| = {N}, r->rho(r) injective: {inj}', flush=True)
        print(f'  involution classes with size/chi_R of a reflection class but not reflections: {clash} '
              f'-> {"every Aut(A)-induced automorphism preserves rho(R)" if not clash else "INCONCLUSIVE"}')
        print(f'  reflection-preserving automorphisms modulo Inn: {len(leaves)}')
        print(f'  good constituents (dim) moved by a simple reflection: {dims_good};  other eigenspaces (dim,<chi,chi>,<chi,perm>): {others}')
        for j, (isstd, ok, v) in enumerate(results):
            print(f'  class {j}: {"identity" if isstd else "non-identity tuple"}; pi realises theta: {ok}; criterion: {v if v else "FAILS (no good constituent with witnesses)"}')
        print(f'  [{name} {time.time() - t0:.1f}s]', flush=True)
    return out

# Expected outcomes (the paper's claims).  Odd dihedral m with 3 \nmid m are INTENDED NEGATIVE results.
POSITIVE = {'A2', 'A3', 'A4', 'A5', 'A6', 'A7', 'B3', 'B4', 'B5', 'B6', 'B7', 'D4', 'D5', 'D6', 'D7',
            'E6', 'E7', 'F4', 'H3', 'H4', 'I2(3)', 'I2(9)', 'I2(15)', 'I2(21)'}
NEGATIVE = {'I2(5)', 'I2(7)', 'I2(11)', 'I2(13)', 'I2(17)', 'I2(19)'}
if __name__ == '__main__':
    FAIL = []
    for nm in sys.argv[1:]:
        o = analyze(nm)
        allok = all(ok and v for _, ok, v in o['results']) and not o['clash']
        if nm in POSITIVE and not allok: FAIL.append(nm)
        if nm in NEGATIVE:
            print(f'  [{nm}: INTENDED NEGATIVE RESULT -- the criterion is expected to fail here]')
            if any(v for _, _, v in o['results']) or o['good']: FAIL.append(nm + ' (expected failure did not occur)')
        if nm not in POSITIVE | NEGATIVE: print(f'  [{nm}: informational only (even m: rho not injective on T)]')
    if FAIL: print('FAILED CHECKS:', FAIL); sys.exit(1)
    print('ALL CHECKS PASSED')
