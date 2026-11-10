# Independent check for E6, E7, E8 (exceptional graph constituents). Imports nothing from the package.
# Integer coordinates: all vectors are doubled (so E8 roots have integer entries, norm 8).
import itertools, sys
import numpy as np
from fractions import Fraction

# Exact rational rank over Q.
def exact_rank(rows):
    from sympy import QQ
    from sympy.polys.matrices import DomainMatrix
    rows = [list(r) for r in rows]
    if not rows: return 0
    return DomainMatrix([[QQ(int(x)) for x in r] for r in rows], (len(rows), len(rows[0])), QQ).rank()
FAIL = []
EXPECT = {"E6": ((36, 15, 6, 6), 15, 20, (30, 5, 12, 3, 12, 4, 20)),
          "E7": ((63, 30, 13, 15), 35, 27, (60, 6, 26, 5, 30, 5, 32)),
          "E8": ((120, 63, 30, 36), 84, 35, (126, 7, 60, 6, 72, 6, 56))}

def e8_roots():
    R = set()
    for i, j in itertools.combinations(range(8), 2):
        for si in (2, -2):
            for sj in (2, -2):
                v = [0]*8; v[i] = si; v[j] = sj; R.add(tuple(v))
    for signs in itertools.product((1, -1), repeat=8):
        if signs.count(-1) % 2 == 0:
            R.add(tuple(signs))
    return sorted(R)

def ip(a, b): return sum(x*y for x, y in zip(a, b))

E8 = e8_roots()
assert len(E8) == 240
# Bourbaki simple roots (doubled), 0-based coords
a1 = (1, -1, -1, -1, -1, -1, -1, 1)
a2 = (2, 2, 0, 0, 0, 0, 0, 0)
def ek(i): v = [0]*8; v[i] = 2; return v
simple = [a1, a2] + [tuple(np.array(ek(k-2)) - np.array(ek(k-3))) for k in range(3, 9)]
simple = [tuple(int(x) for x in s) for s in simple]
for s in simple: assert s in set(E8), s

def subsystem(n):
    S = simple[:n]
    # roots of E8 in span of S: integer solve via rank test
    out = []
    for r in E8:
        if exact_rank(list(S) + [r]) == n: out.append(r)
    return out

def refl(r, x):
    c = Fraction(2*ip(x, r), ip(r, r))
    assert c.denominator == 1
    return tuple(xi - int(c)*ri for xi, ri in zip(x, r))

def line(v):
    w = tuple(-x for x in v)
    return max(v, w)

def intbasis(M):
    from sympy import lcm
    K = M.nullspace().to_Matrix()   # rows span kernel
    rows = []
    for i in range(K.rows):
        row = list(K.row(i)); L = 1
        for x in row: L = lcm(L, x.q)
        rows.append([int(x*L) for x in row])
    return np.array(rows, dtype=object).reshape(K.rows, K.cols).T

def analyse(name, n, expect):
    Phi = subsystem(n)
    lines = sorted({line(r) for r in Phi})
    idx = {l: i for i, l in enumerate(lines)}
    N = len(lines)
    gens = []
    for s in simple[:n]:
        gens.append([idx[line(refl(s, l))] for l in lines])
    # check closure: reflections in all roots map lines to lines -> fine via idx lookups
    # orbitals by union-find on ordered pairs
    parent = list(range(N*N))
    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]; a = parent[a]
        return a
    for g in gens:
        for a in range(N):
            ga = g[a]
            for b in range(N):
                x, y = find(a*N+b), find(ga*N+g[b])
                if x != y: parent[x] = y
    orb = {}
    for p in range(N*N): orb.setdefault(find(p), []).append(p)
    norb = len(orb)
    # check orbitals = equality / orthogonal / non-orthogonal
    G = np.array([[ip(a, b) for b in lines] for a in lines])
    labels = set()
    for o in orb.values():
        ty = {('eq' if a == b else ('perp' if G[a, b] == 0 else 'nonperp')) for p in o for a, b in [divmod(p, N)]}
        labels.add(tuple(sorted(ty)))
    A = (G == 0).astype(np.int64)
    k = A[0].sum()
    J = np.ones((N, N), dtype=np.int64); I = np.eye(N, dtype=np.int64)
    A2 = A @ A
    lam = {A2[a, b] for a in range(N) for b in range(N) if a != b and A[a, b]}
    mu = {A2[a, b] for a in range(N) for b in range(N) if a != b and not A[a, b]}
    assert len(lam) == 1 and len(mu) == 1
    lam = lam.pop(); mu = mu.pop()
    srg_ok = np.array_equal(A2, k*I + lam*A + mu*(J - I - A))
    # eigenvalues r,s (integers) from quadratic x^2 - (lam-mu) x - (k-mu)
    disc = (lam - mu)**2 + 4*(k - mu)
    sq = int(round(disc**0.5)); assert sq*sq == disc
    r = ((lam - mu) + sq)//2; s = ((lam - mu) - sq)//2
    # exact: (A - rI)(A - sI) = mu J on whole space; ranks exact via sympy
    from sympy.polys.matrices import DomainMatrix
    from sympy import ZZ, QQ
    def dm(M): return DomainMatrix([[ZZ(int(x)) for x in row] for row in M], (N, N), ZZ)
    Ar = dm(A - r*I).convert_to(QQ); As = dm(A - s*I).convert_to(QQ)
    fr = N - Ar.rank(); fs = N - As.rank()
    trace_ok = (k + r*fr + s*fs == 0) and (1 + fr + fs == N)
    print(f"{name}: lines={N} orbitals={norb} types={sorted(labels)} SRG=({N},{k},{lam},{mu}) identity={srg_ok}")
    print(f"   eigenvalues {k}^1 {r}^{fr} {s}^{fs} (exact ranks over Q; trace check {trace_ok}); expect {expect}")
    if not (srg_ok and norb == 3 and labels == {('eq',), ('perp',), ('nonperp',)}
            and (N, k, lam, mu) == EXPECT[name][0] and (fr, fs) == EXPECT[name][1:3] and trace_ok):
        FAIL.append(name + ' SRG/orbitals/spectrum'); print('   *** CHECK FAILED')
    Kr = intbasis(Ar); Ks = intbasis(As)
    Ao = A.astype(object)
    ok_r = not np.any(Ao.dot(Kr) - r*Kr); ok_s = not np.any(Ao.dot(Ks) - s*Ks)
    ones_ok = not np.any(Kr.sum(axis=0)) and not np.any(Ks.sum(axis=0))
    print(f"   integer eigenbases verified: {ok_r}, {ok_s}; orthogonal to 1 (J acts by 0): {ones_ok}; dims {Kr.shape[1]}, {Ks.shape[1]}")
    nontriv = []
    for K in (Kr, Ks):
        nontriv.append(all(np.any(K[list(g)] - K) for g in gens))
    print(f"   all simple reflections act nontrivially on both eigenspaces: {nontriv}")
    for description, ok in [
        ('eigenbasis identities', ok_r and ok_s),
        ('constant-vector orthogonality', ones_ok),
        ('complete independent eigenbases',
         (Kr.shape[1], Ks.shape[1]) == (fr, fs)
         and (exact_rank(Kr.T), exact_rank(Ks.T)) == (fr, fs)),
        ('nontrivial simple-reflection actions', all(nontriv)),
    ]:
        if not ok:
            FAIL.append(name + ' ' + description); print('   *** CHECK FAILED:', description)
    # perpendicular subsystem counts and ranks
    a0 = simple[0]
    perp = [x for x in Phi if ip(x, a0) == 0]
    g0 = [x for x in perp if x != a0][0]
    pp = [x for x in Phi if ip(x, a0) == 0 and ip(x, g0) == 0]
    b0 = [x for x in Phi if ip(x, a0) == 4][0]  # (a,b)=1 after undoubling
    pb = [x for x in Phi if ip(x, a0) == 0 and ip(x, b0) == 0]
    rk = exact_rank
    print(f"   perp counts (rank): a^perp {len(perp)}({rk(perp)}), {{a,g}}^perp {len(pp)}({rk(pp)}), {{a,b}}^perp {len(pb)}({rk(pb)})")
    nb = len([x for x in Phi if ip(x, a0) == 4])
    print(f"   roots with (a,b)=1: {nb}   [ranks exact over Q]")
    got = (len(perp), rk(perp), len(pp), rk(pp), len(pb), rk(pb), nb)
    if got != EXPECT[name][3]: FAIL.append(name + ' perp counts/ranks'); print('   *** CHECK FAILED', got)

def main():
    FAIL.clear()
    for name, n, e in [("E6", 6, "3^15 (-3)^20"), ("E7", 7, "3^35 (-5)^27"), ("E8", 8, "3^84 (-9)^35")]:
        analyse(name, n, e)
        sys.stdout.flush()
    if FAIL:
        print("FAILED CHECKS:", FAIL)
        return 1
    print("ALL CHECKS PASSED (SRG identities, orbitals, exact eigenbases, reflection actions and perpendicular subsystems)")
    return 0

if __name__ == '__main__':
    sys.exit(main())
