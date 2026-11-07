# Independent check for D4, D5 (and B_n), F4, H3. Imports nothing from the package.
# NOTE: this checker uses NUMERICAL linear algebra (QR, pseudoinverse, rounded characters).
# It is numerical corroboration only. The exact companion checks are explicit_constituents.py (h3, f4, d4, bd)
# and indep_check.py.
import itertools, sys
from fractions import Fraction as F
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from quadratic_field import Q5, PHI, PHIi

def run_group(gens, N):
    idp = tuple(range(N)); G = {idp}; fr = [idp]
    while fr:
        nf = []
        for g in fr:
            for s in gens:
                h = tuple(s[g[i]] for i in range(N))
                if h not in G: G.add(h); nf.append(h)
        fr = nf
    return sorted(G)

def pm(g, N):
    M = np.zeros((N, N))
    for i in range(N): M[g[i], i] = 1
    return M

def char_data(G, N, Bn):
    Q, _ = np.linalg.qr(Bn); Pu = Q @ Q.T
    chi = np.array([np.trace(Pu @ pm(g, N)) for g in G])
    chiT = np.array([sum(1 for i in range(N) if g[i] == i) for g in G])
    inv_ok = all(np.allclose(pm(g, N) @ Bn, Pu @ pm(g, N) @ Bn, atol=1e-8) for g in G[:: max(1, len(G)//200)])
    return round(float(chi @ chi)/len(G), 6), round(float(chi @ chiT)/len(G), 6), inv_ok

def eigdims(M, U):
    pinv = np.linalg.pinv(U); X = pinv @ M @ U
    assert np.allclose(U @ X, M @ U, atol=1e-8)
    d = U.shape[1]
    return (d - np.linalg.matrix_rank(X - np.eye(d), tol=1e-7), d - np.linalg.matrix_rank(X + np.eye(d), tol=1e-7))

# ---------------- integer root systems (rational coords) ----------------
def refl(r, x):
    c = F(2*sum(a*b for a, b in zip(x, r)), sum(a*a for a in r))
    return tuple(xi - c*ri for xi, ri in zip(x, r))
def line(v):
    w = tuple(-a for a in v); return max(tuple(v), w)

def setup(roots, simple):
    lines = sorted({line(r) for r in roots}); idx = {l: i for i, l in enumerate(lines)}
    gens = [tuple(idx[line(refl(s, l))] for l in lines) for s in simple]
    return lines, idx, gens

def Dn(n, B=False):
    R = []
    for i, j in itertools.combinations(range(n), 2):
        for a in (1, -1):
            for b in (1, -1):
                v = [F(0)]*n; v[i] = F(a); v[j] = F(b); R.append(tuple(v))
    if B:
        for i in range(n):
            for a in (1, -1):
                v = [F(0)]*n; v[i] = F(a); R.append(tuple(v))
    simple = []
    for i in range(n-1):
        v = [F(0)]*n; v[i] = F(1); v[i+1] = F(-1); simple.append(tuple(v))
    v = [F(0)]*n
    if B: v[n-1] = F(1)
    else: v[n-2] = F(1); v[n-1] = F(1)
    simple.append(tuple(v))
    return R, simple

def Uminus(n, lines, idx):
    N = len(lines); cols = []; pairs = []
    for i, j in itertools.combinations(range(n), 2):
        p = [F(0)]*n; p[i] = F(1); p[j] = F(1)
        m = [F(0)]*n; m[i] = F(1); m[j] = F(-1)
        u = np.zeros(N); u[idx[line(p)]] = 1; u[idx[line(m)]] = -1
        cols.append(u); pairs.append((i, j))
    return np.array(cols).T, pairs

for name, n, B in [("D4", 4, False), ("D5", 5, False), ("D6", 6, False), ("B3", 3, True), ("B4", 4, True), ("B5", 5, True)]:
    R, S = Dn(n, B)
    lines, idx, gens = setup(R, S)
    N = len(lines)
    G = run_group(gens, N)
    U, pairs = Uminus(n, lines, idx)
    nn, nt, inv = char_data(G, N, U)
    print(f"{name}: |T|={N} |rho(W)|={len(G)} U^-: dim {U.shape[1]} invariant {inv} <chi,chi>={nn} <chi,chi_T>={nt}")
    if not B and n >= 5:
        # negate e_n witness
        neg = lambda v: tuple(list(v[:-1]) + [-v[-1]])
        pi = tuple(idx[line(neg(l))] for l in lines)
        print(f"   negate e_n: normalises {all(tuple(pi[s[pi[i]]] for i in range(N)) in set(G) for s in gens)}, in rho(W): {pi in set(G)}, dims(+1,-1) on U^-: {eigdims(pm(pi, N), U)}")
    if name == "D4":
        # J: u_ij -> u_kl
        comp = {p: tuple(sorted(set(range(4)) - set(p))) for p in pairs}
        Jm = np.zeros((6, 6))
        for a, p in enumerate(pairs): Jm[pairs.index(comp[p]), a] = 1
        pinv = np.linalg.pinv(U)
        comm = all(np.allclose((pinv @ pm(g, N) @ U) @ Jm, Jm @ (pinv @ pm(g, N) @ U)) for g in G)
        print("   J commutes with W(D4) on U^-:", comm)
        for sgn in (1, -1):
            w, v = np.linalg.eigh(Jm); Ue = U @ v[:, np.isclose(w, sgn)]
            print(f"   J={sgn:+d} eigenspace dim {Ue.shape[1]}: <chi,chi>, <chi,chi_T>, invariant =", char_data(G, N, Ue))
        # frames: maximal sets of 4 mutually orthogonal lines
        L = np.array([[float(x) for x in l] for l in lines]); Gm = L @ L.T
        frames = sorted({tuple(sorted([a] + [b for b in range(N) if abs(Gm[a, b]) < 1e-9])) for a in range(N)})
        print("   frames:", len(frames), [len(f) for f in frames])
        fr_of = {x: i for i, f in enumerate(frames) for x in f}
        Uf = np.array([[(1 if fr_of[x] == i else 0) - (1 if fr_of[x] == 2 else 0) for x in range(N)] for i in range(2)]).T.astype(float)
        print("   frame module dim 2: <chi,chi>, <chi,chi_T>, invariant =", char_data(G, N, Uf))
        # graph automorphisms realised by linear maps permuting simple roots (S[1] is the central node)
        Sm = np.array([[float(x) for x in s] for s in S])
        outer = [0, 2, 3]
        for perm in itertools.permutations(outer):
            target = list(range(4));
            for a, b in zip(outer, perm): target[a] = b
            T = np.linalg.solve(Sm, Sm[target])   # rows: Sm @ T = Sm[target]  -> v -> v @ T
            img = []
            for l in lines:
                v = np.array([float(x) for x in l]) @ T
                key = None
                for m, l2 in enumerate(lines):
                    if np.allclose(v, [float(x) for x in l2]) or np.allclose(-v, [float(x) for x in l2]): key = m
                img.append(key)
            pi = tuple(img)
            assert None not in pi
            norm = all(tuple(pi[s[pi.index(i)]] for i in range(N)) in set(G) for s in gens)
            dims = set()
            for h in G:
                hp = tuple(h[pi[i]] for i in range(N))
                dims.add(tuple(int(x) for x in eigdims(pm(hp, N), Uf)))
            print(f"   graph aut {perm}: normalises {norm}; (dim+1,dim-1) of h*pi on frame module over h: {sorted(dims)}")

# ---------------- F4 ----------------
R = []
for i, j in itertools.combinations(range(4), 2):
    for a in (1, -1):
        for b in (1, -1):
            v = [F(0)]*4; v[i] = F(a); v[j] = F(b); R.append(tuple(v))
for i in range(4):
    for a in (1, -1):
        v = [F(0)]*4; v[i] = F(a); R.append(tuple(v))
for sg in itertools.product((1, -1), repeat=4): R.append(tuple(F(s, 2) for s in sg))
S = [(F(0), F(1), F(-1), F(0)), (F(0), F(0), F(1), F(-1)), (F(0), F(0), F(0), F(1)), (F(1, 2), F(-1, 2), F(-1, 2), F(-1, 2))]
lines, idx, gens = setup(R, S); N = len(lines)
G = run_group(gens, N)
print(f"F4: |T|={N} |rho(W)|={len(G)}")
L = np.array([[float(x) for x in l] for l in lines]); Gm = L @ L.T
islong = [abs(Gm[a, a] - 2) < 1e-9 for a in range(N)]
frames = sorted({tuple(sorted([a] + [b for b in range(N) if abs(Gm[a, b]) < 1e-9 and islong[b] == islong[a]])) for a in range(N)})
print("   frames (orthogonal within class):", [(len(f), islong[f[0]]) for f in frames])
fr_of = {x: i for i, f in enumerate(frames) for x in f}
def frmod(long):
    fl = [i for i, f in enumerate(frames) if islong[f[0]] == long]
    return np.array([[(1 if fr_of[x] == fl[k] else 0) - (1 if fr_of[x] == fl[2] else 0) for x in range(N)] for k in range(2)]).T.astype(float)
Ul, Us = frmod(True), frmod(False)
print("   U_long: <chi,chi>, <chi,chi_T>, inv =", char_data(G, N, Ul), " U_short:", char_data(G, N, Us))
for k, s in enumerate(gens):
    print(f"   simple refl {k}: nontrivial on U_long {not np.allclose(pm(s, N) @ Ul, Ul)}, on U_short {not np.allclose(pm(s, N) @ Us, Us)}")
Lmap = lambda v: (v[0]+v[1], v[0]-v[1], v[2]+v[3], v[2]-v[3])
def find_line(v):
    for m, l in enumerate(lines):
        # proportional?
        a = np.array([float(x) for x in v]); b = np.array([float(x) for x in l])
        if abs(abs(a @ b) - np.linalg.norm(a)*np.linalg.norm(b)) < 1e-9: return m
piL = tuple(find_line(Lmap(l)) for l in lines)
print("   pi_L permutation:", sorted(piL) == list(range(N)), " normalises:", all(tuple(piL[s[piL.index(i)]] for i in range(N)) in set(G) for s in gens),
      " pi_L^2 = 1:", all(piL[piL[i]] == i for i in range(N)))
PL = pm(piL, N)
def same_space(A, B): return np.linalg.matrix_rank(np.hstack([A, B]), tol=1e-8) == A.shape[1] == B.shape[1]
print("   pi_L U_long = U_short:", same_space(PL @ Ul, Us), " pi_L U_short = U_long:", same_space(PL @ Us, Ul))
s0 = pm(gens[0], N)  # long simple reflection
Q2 = (s0 @ PL) @ (s0 @ PL)
print("   (s pi_L)^2 dims (+1,-1) on U_short:", eigdims(Q2, Us), "; pi_L^2 on U_short:", eigdims(PL @ PL, Us))
# swap witness for every h: which (+1,-1) eigenvectors of (h pi)^2 exist in U_short
dims = set()
for h in G:
    Q = pm(h, N) @ PL; dims.add(tuple(int(x) for x in eigdims(Q @ Q, Us)))
print("   over all h: dims of (h pi_L)^2 on U_short:", sorted(dims))

# ---------------- H3 ----------------
Zq, Oq = Q5(0), Q5(1)
def kq(x): return tuple(c.key() for c in x)
def canon(x):
    for c in x:
        if not c.iszero(): return x if c.ispos() else tuple(-a for a in x)
EVEN3 = [(0, 1, 2), (1, 2, 0), (2, 0, 1)]
R3 = []
for i in range(3):
    for s in (2, -2):
        v = [Zq]*3; v[i] = Q5(s); R3.append(tuple(v))
base = [PHI, Oq, PHIi]
for p in EVEN3:
    for sg in itertools.product((1, -1), repeat=3):
        v = [None]*3
        for i in range(3): v[p[i]] = base[i]*sg[i]
        R3.append(tuple(v))
def ip3(x, y): return x[0]*y[0] + x[1]*y[1] + x[2]*y[2]
def refl3(r, x):
    c = (ip3(x, r)*2)/ip3(r, r); return tuple(a - c*b for a, b in zip(x, r))
Rk = {kq(r) for r in R3}
print(f"H3: {len(R3)} roots, closed under reflections: {all(kq(refl3(r, x)) in Rk for r in R3 for x in R3)}")
lines3 = sorted({kq(canon(r)) for r in R3}); lidx = {l: i for i, l in enumerate(lines3)}
lv = {kq(canon(r)): canon(r) for r in R3}
N3 = len(lines3)
gens3 = [tuple(lidx[kq(canon(refl3(lv[r], lv[l])))] for l in lines3) for r in lines3]
G3 = run_group(gens3, N3)
print(f"   |T|={N3} |rho(W)|={len(G3)}")
orth = [[ip3(lv[a], lv[b]).iszero() for b in lines3] for a in lines3]
frames3 = sorted({tuple(sorted([a] + [b for b in range(N3) if orth[a][b]])) for a in range(N3)})
print("   frames:", len(frames3), [len(f) for f in frames3])
f3 = {x: i for i, f in enumerate(frames3) for x in f}
U3 = np.array([[(1 if f3[x] == k else 0) - (1 if f3[x] == 4 else 0) for x in range(N3)] for k in range(4)]).T.astype(float)
print("   frame module: <chi,chi>, <chi,chi_T>, inv =", char_data(G3, N3, U3))
Sigma = lambda x: (x[0].conj(), x[2].conj(), x[1].conj())   # sigma then swap last two coords
print("   Sigma preserves roots:", all(kq(Sigma(r)) in Rk for r in R3))
piS = tuple(lidx[kq(canon(Sigma(lv[l])))] for l in lines3)
print("   pi_Sigma normalises:", all(tuple(piS[s[piS.index(i)]] for i in range(N3)) in set(G3) for s in gens3), " in rho(W):", piS in set(G3))
stab = [g for g in G3 if g[0] == 0]
print("   points fixed by Stab(line 0):", sum(1 for x in range(N3) if all(g[x] == x for g in stab)), "(>1 would mean nontrivial centraliser)")
fa = sorted(set((f3[x], f3[piS[x]]) for x in range(N3)))
cyc = [i for i in range(5) if dict(fa)[i] == i]
print("   pi_Sigma on frames:", dict(fa), " fixed frames:", len(cyc), " dims on U:", eigdims(pm(piS, N3), U3))
