# Referee's independent check for E6, E7, E8 (Prop 4.2). Imports nothing from the package.
# Integer coordinates: all vectors are doubled (so E8 roots have integer entries, norm 8).
import itertools, sys
import numpy as np
from fractions import Fraction

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
    M = np.array(S, dtype=float)
    out = []
    for r in E8:
        A = np.vstack([M, r])
        if np.linalg.matrix_rank(A) == n: out.append(r)
    return out

def refl(r, x):
    c = Fraction(2*ip(x, r), ip(r, r))
    assert c.denominator == 1
    return tuple(xi - int(c)*ri for xi, ri in zip(x, r))

def line(v):
    w = tuple(-x for x in v)
    return max(v, w)

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
    from sympy import ZZ, QQ, lcm
    def dm(M): return DomainMatrix([[ZZ(int(x)) for x in row] for row in M], (N, N), ZZ)
    Ar = dm(A - r*I).convert_to(QQ); As = dm(A - s*I).convert_to(QQ)
    fr = N - Ar.rank(); fs = N - As.rank()
    trace_ok = (k + r*fr + s*fs == 0) and (1 + fr + fs == N)
    print(f"{name}: lines={N} orbitals={norb} types={sorted(labels)} SRG=({N},{k},{lam},{mu}) identity={srg_ok}")
    print(f"   eigenvalues {k}^1 {r}^{fr} {s}^{fs} (exact ranks over Q; trace check {trace_ok}); expect {expect}")
    def intbasis(M):
        K = M.nullspace().to_Matrix()   # rows span kernel
        rows = []
        for i in range(K.rows):
            row = list(K.row(i)); L = 1
            for x in row: L = lcm(L, x.q)
            rows.append([int(x*L) for x in row])
        return np.array(rows, dtype=object).T     # N x d integer
    Kr = intbasis(Ar); Ks = intbasis(As)
    Ao = A.astype(object)
    ok_r = not np.any(Ao.dot(Kr) - r*Kr); ok_s = not np.any(Ao.dot(Ks) - s*Ks)
    ones_ok = not np.any(Kr.sum(axis=0)) and not np.any(Ks.sum(axis=0))
    print(f"   integer eigenbases verified: {ok_r}, {ok_s}; orthogonal to 1 (J acts by 0): {ones_ok}; dims {Kr.shape[1]}, {Ks.shape[1]}")
    nontriv = []
    for K in (Kr, Ks):
        nontriv.append(all(np.any(K[list(g)] - K) for g in gens))
    print(f"   all simple reflections act nontrivially on both eigenspaces: {nontriv}")
    # perpendicular subsystem counts and ranks
    a0 = simple[0]
    perp = [x for x in Phi if ip(x, a0) == 0]
    g0 = [x for x in perp if x != a0][0]
    pp = [x for x in Phi if ip(x, a0) == 0 and ip(x, g0) == 0]
    b0 = [x for x in Phi if ip(x, a0) == 4][0]  # (a,b)=1 after undoubling
    pb = [x for x in Phi if ip(x, a0) == 0 and ip(x, b0) == 0]
    rk = lambda L: np.linalg.matrix_rank(np.array(L, dtype=float)) if L else 0
    print(f"   perp counts (rank): a^perp {len(perp)}({rk(perp)}), {{a,g}}^perp {len(pp)}({rk(pp)}), {{a,b}}^perp {len(pb)}({rk(pb)})")
    nb = len([x for x in Phi if ip(x, a0) == 4])
    print(f"   roots with (a,b)=1: {nb}")

for name, n, e in [("E6", 6, "3^15 (-3)^20"), ("E7", 7, "3^35 (-5)^27"), ("E8", 8, "3^84 (-9)^35")]:
    analyse(name, n, e)
    sys.stdout.flush()
