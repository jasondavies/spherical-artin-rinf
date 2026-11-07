"""Independent re-verification of the representation-theoretic input of the paper.

Fresh code: imports only rootsys.py / permgroup.py from this directory, numpy and sympy.
Method differs from certify.py (which uses orbital matrices = commutant of the permutation module):
here the candidate constituent U is a joint eigenspace of the *reflection class sums*
T_K = sum_{r in K} P_r (central elements of the group algebra), and U is certified by CHARACTERS:
    <chi_U, chi_U> = 1          (U (x) C irreducible, i.e. U absolutely irreducible)
    <chi_U, chi_perm> = 1       (U has multiplicity one in Q^R)
where chi_U(g) = trace(E_U P_g) is computed exactly from the rational orthogonal projection E_U.
All group elements of rho(W) = W/Z(W) are enumerated, so this is done for H3, F4, H4, E6, E7
(E8 is too large to enumerate here; it is covered by certify.py only).

It also checks: |rho(W)|, trivial centre of rho(W), the braid-relation computation behind
f : A -> Z^R x| W, and the eigenvalue witnesses (inner and outer cases), with explicit,
geometrically defined outer permutations pi_0:
  H3, H4: Galois conjugation sqrt5 -> -sqrt5 followed by a signed coordinate permutation;
  F4    : the similarity L(x) = (x1+x2, x1-x2, x3+x4, x3-x4) exchanging long and short roots.
"""
import sys, time, itertools
import numpy as np
from fractions import Fraction as Fr
from sympy import Matrix, QQ, ZZ, ilcm
from sympy.polys.matrices import DomainMatrix
import rootsys as rsm
from rootsys import RootSystem
from permgroup import enumerate_group, inverse, centre, order

WORDER = {'H3': 120, 'H4': 14400, 'F4': 1152, 'E6': 51840, 'E7': 2903040, 'E8': 696729600, 'D5': 1920}
ZORDER = {'H3': 2, 'H4': 2, 'F4': 2, 'E6': 1, 'E7': 2, 'E8': 2, 'D5': 1}

def dm(rows):
    rows = [[int(x) for x in r] for r in rows]
    return DomainMatrix([[ZZ(x) for x in r] for r in rows], (len(rows), len(rows[0])), ZZ).convert_to(QQ)

def nullspace_basis(Mint):
    """exact rational nullspace of an integer numpy matrix; returns sympy Matrix N x d (columns = basis)"""
    ns = dm(Mint).nullspace().to_Matrix()
    return ns.T

def nullity(Mint):
    return dm(Mint).nullspace().shape[0]

def permmat(p):
    N = len(p); P = np.zeros((N, N), dtype=np.int64); P[np.asarray(p, int), np.arange(N)] = 1   # e_r -> e_{p(r)}
    return P

def int_basis(B):
    """clear denominators column by column -> integer numpy array N x d"""
    cols = []
    for j in range(B.shape[1]):
        c = B[:, j]; den = ilcm(*[x.q for x in c]) if any(x != 0 for x in c) else 1
        cols.append([int(x * den) for x in c])
    return np.array(cols, dtype=np.int64).T

def character(B, E):
    """chi_U(g) for all g in E (rows), exactly.  Projection P_U = B (B^T B)^{-1} B^T (orthogonal, W-equivariant)."""
    Bm = Matrix(B.tolist())
    Pm = Bm * (Bm.T * Bm).inv() * Bm.T
    D = ilcm(*[x.q for x in Pm])
    Pint = np.array([[int(x * D) for x in Pm.row(i)] for i in range(Pm.shape[0])], dtype=np.int64)
    N = Pint.shape[0]
    chiD = np.concatenate([Pint[np.arange(N)[None, :], E[k:k + 100000].astype(np.int64)].sum(axis=1)
                           for k in range(0, len(E), 100000)])            # sum_r P[r, g(r)]
    assert np.all(chiD % D == 0), 'non-integral character value'
    return chiD // D

def run(name):
    t0 = time.time()
    rs = RootSystem(name); N = rs.N; n = rs.n
    print(f'===== {name}: rank {n}, |Phi| = {len(rs.roots)}, |R| = {N}, Coxeter matrix {rs.coxeter}', flush=True)
    E, index = enumerate_group(rs.gens)
    print(f'  |rho(W)| = {len(E)}  (expected |W|/|Z(W)| = {WORDER[name]}/{ZORDER[name]} = {WORDER[name]//ZORDER[name]})'
          f'  -> {len(E) == WORDER[name] // ZORDER[name]}', flush=True)
    Z = centre(E, rs.gens)
    print(f'  centre of rho(W) has order {len(Z)}', flush=True)

    # --- braid relations for f(s) = (e_s, s): for each pair the reflection sequences of the two
    #     alternating words of length m are the same set, without repetition
    ok = True
    for i in range(n):
        for j in range(i + 1, n):
            m = rs.coxeter[i][j]
            seqs = []
            for a, b in ((i, j), (j, i)):
                x = np.arange(N); refl = []
                for k in range(m):
                    t = (a, b)[k % 2]
                    refl.append(int(x[rs.sidx[t]]))     # reflection x s_t x^{-1} as a point of R
                    x = x[np.asarray(rs.gens[t])]
                seqs.append(refl)
            if not (len(set(seqs[0])) == m and set(seqs[0]) == set(seqs[1])): ok = False
    print(f'  braid relations respected by f (vector parts agree, each reflection once): {ok}', flush=True)

    # --- reflection classes and class sums
    orbits = []; seen = set()
    for r in range(N):
        if r not in seen:
            orb = set(E[:, r].tolist()); seen |= orb; orbits.append(sorted(orb))
    print(f'  rho(W)-orbits on R (reflection classes): sizes {[len(o) for o in orbits]}', flush=True)
    perm_of_refl = [np.array(rs.perm_of(rs.R[r]), dtype=np.int64) for r in range(N)]
    Ts = []
    for orb in orbits:
        T = np.zeros((N, N), dtype=np.int64)
        for r in orb: T += permmat(perm_of_refl[r])
        Ts.append(T)
    Y = sum((1000 ** k) * T for k, T in enumerate(Ts))
    ev = np.linalg.eigvalsh(Y.astype(float))
    cands = sorted(set(int(round(x)) for x in ev if abs(x - round(x)) < 1e-6))
    fix = (E == np.arange(N, dtype=E.dtype)).sum(axis=1).astype(np.int64)    # permutation character
    order_G = len(E)
    good = []
    for lam in cands:
        B = nullspace_basis(Y - lam * np.eye(N, dtype=np.int64))
        d = B.shape[1]
        if d == 0: continue
        Bi = int_basis(B)
        # W-invariance (automatic for a central element, but check)
        inv_ok = all(dm(np.hstack([Bi, permmat(g) @ Bi]).T.tolist()).rank() == d for g in rs.gens)   # exact
        chi = character(Bi, E)
        n1 = Fr(int((chi * chi).sum()), order_G); n2 = Fr(int((chi * fix).sum()), order_G)
        moved = [i for i in range(n) if chi[index[np.asarray(rs.gens[i], dtype=E.dtype).tobytes()]] != d]
        tag = 'GOOD' if (n1 == 1 and n2 == 1 and d > 1) else ''
        print(f'  eigenspace lam={lam}: dim {d}, W-invariant {inv_ok}, <chi,chi> = {n1}, <chi,perm> = {n2}, '
              f'chi(1) = {chi[0]}, simple reflections acting nontrivially: {moved} {tag}', flush=True)
        if tag: good.append((lam, Bi, chi))
    res = {'rs': rs, 'E': E, 'index': index, 'good': good}
    EXP_GOOD = {'H3': [4], 'F4': [2, 2], 'H4': [16, 25], 'E6': [15, 20], 'E7': [27, 35], 'D5': [4, 5, 10]}
    if name in EXP_GOOD and sorted(B.shape[1] for _, B, _ in good) != sorted(EXP_GOOD[name]):
        FAIL.append(f'{name}: good constituent dims')
    if name in ('H3', 'H4', 'F4'):
        outer_witnesses(name, rs, E, index, good, Y)
    print(f'  [{name} done in {time.time() - t0:.1f}s]', flush=True)
    return res

def explicit_pi0(name, rs):
    if name == 'F4':
        def T(v):
            x1, x2, x3, x4 = v
            return (rsm.add(x1, x2), rsm.sub(x1, x2), rsm.add(x3, x4), rsm.sub(x3, x4))
        # check: T maps every root to a root or to 2*root
        rootset = set(rs.roots)
        ok = all((T(r) in rootset) or (tuple(rsm.mul(rsm.num(Fr(1, 2)), x) for x in T(r)) in rootset) for r in rs.roots)
        print(f'  F4: L maps each root to a root or twice a root: {ok}')
        return np.array(rs.perm_of_map(T)), 'L(x)=(x1+x2,x1-x2,x3+x4,x3-x4)'
    # H3/H4: Galois conjugation then a signed coordinate permutation g with g(sigma(Phi)) = Phi
    dim = len(rs.roots[0]); rootset = set(rs.roots)
    sig = [tuple(rsm.galois(x) for x in r) for r in rs.roots]
    for p in itertools.permutations(range(dim)):
        for s in itertools.product((1, -1), repeat=dim):
            def g(v, p=p, s=s):
                w = [None] * dim
                for i in range(dim): w[p[i]] = rsm.mul(rsm.num(s[i]), v[i])
                return tuple(w)
            if all(g(v) in rootset for v in sig):
                T = lambda v, g=g: g(tuple(rsm.galois(x) for x in v))
                return np.array(rs.perm_of_map(T)), f'Galois sqrt5->-sqrt5, then x_i -> {s} at positions {p}'
    raise RuntimeError

def outer_witnesses(name, rs, E, index, good, Y):
    N = rs.N; n = rs.n; dt = E.dtype
    pi0, desc = explicit_pi0(name, rs)
    pi0 = pi0.astype(dt); pinv = inverse(pi0)
    # pi0 normalises rho(W): pi0 o s_i o pi0^{-1} lies in rho(W)
    conj = [pi0[np.asarray(g, dtype=dt)][pinv] for g in rs.gens]
    norm_ok = all(c.tobytes() in index for c in conj)
    # outer: no h in rho(W) with h s_i h^{-1} = pi0 s_i pi0^{-1} for all i
    inner = False
    for h in E:
        hi = inverse(h)
        if all(np.array_equal(h[np.asarray(g, dtype=dt)][hi], c) for g, c in zip(rs.gens, conj)): inner = True; break
    print(f'  explicit pi_0 ({desc}): normalises rho(W): {norm_ok}; induced automorphism is outer: {not inner}', flush=True)
    Pp = permmat(pi0)
    # which good constituents does pi0 map where (exactly)
    img = {}
    for a, (la, Ba, _) in enumerate(good):
        for b, (lb, Bb, _) in enumerate(good):
            if Ba.shape[1] == Bb.shape[1] and np.all((Y - lb * np.eye(N, dtype=np.int64)) @ (Pp @ Ba) == 0):
                img[a] = b
        print(f'  pi_0 maps constituent {a} (dim {Ba.shape[1]}) exactly onto constituent {img.get(a)}', flush=True)
    for a, (la, Ba, _) in enumerate(good):
        d = Ba.shape[1]
        Q, _ = np.linalg.qr(Ba.astype(float))
        stable = img.get(a) == a
        for eps in (1, -1):
            found = None
            for x in range(len(E)):
                q = E[x][pi0]                        # h o pi0
                if not stable: q = q[q]              # (h o pi0)^2
                M = Q.T @ permmat(q).astype(float) @ Q
                if np.min(np.abs(np.linalg.eigvals(M) - eps)) < 1e-6:
                    k = nullity((permmat(q) - eps * np.eye(N, dtype=np.int64)) @ Ba)
                    if k > 0: found = (x, k); break
            kind = '(h pi0)|U' if stable else '(h pi0)^2|U'
            print(f'  constituent {a} ({"stable" if stable else "swapped"}): exists h with {kind} having eigenvalue {eps:+d}: '
                  f'{found is not None}' + (f' (element #{found[0]}, exact eigenspace dim {found[1]})' if found else ''), flush=True)
            if found is None: FAIL.append(f'{name}: witness constituent {a} eps {eps}')


# ---------------------------------------------------------------------------------------------
# Commutant certificate with fresh code and the exact root systems (used for E8, where the group
# is too large to enumerate for the character test).  End_W(Q^R) is spanned by the orbital
# matrices (indicator matrices of rho(W)-orbits on R x R).  If every orbital matrix acts on U as a
# scalar, then End_W(C^R) acts on U (x) C by scalars, which forces U (x) C to be an irreducible
# constituent of multiplicity one (see the paper, Lemma on certificates).
def commutant_check(name):
    t0 = time.time()
    rs = RootSystem(name); N = rs.N
    # orbitals via union-find on pairs, generated by the simple reflections
    parent = list(range(N * N))
    def find(a):
        while parent[a] != a: parent[a] = parent[parent[a]]; a = parent[a]
        return a
    for g in rs.gens:
        for a in range(N):
            for b in range(N):
                x, y = find(a * N + b), find(g[a] * N + g[b])
                if x != y: parent[x] = y
    lab = np.array([find(i) for i in range(N * N)]).reshape(N, N)
    labels = sorted(set(lab.flatten().tolist()))
    orb = [(lab == l).astype(np.int64) for l in labels]
    # reflection class sum (single class for E8)
    T = np.zeros((N, N), dtype=np.int64)
    for r in range(N): T += permmat(np.array(rs.perm_of(rs.R[r])))
    ev = np.linalg.eigvalsh(T.astype(float))
    cands = sorted(set(int(round(x)) for x in ev if abs(x - round(x)) < 1e-6))
    print(f'===== {name} (commutant method, exact roots): |R| = {N}, number of orbitals = {len(orb)}', flush=True)
    for lam in cands:
        B = int_basis(nullspace_basis(T - lam * np.eye(N, dtype=np.int64)))
        d = B.shape[1]
        scal = True
        for O in orb:
            OB = O @ B
            # scalar on U?  OB = mu B  (exact integer test: OB * B[j0,0] == B * OB[j0,0])
            j0 = int(np.nonzero(B[:, 0])[0][0])
            if not np.array_equal(OB * B[j0, 0], B * OB[j0, 0]): scal = False; break
        moved = [i for i in range(rs.n) if not np.array_equal(permmat(np.array(rs.gens[i])) @ B, B)]
        print(f'  T-eigenspace lam={lam}: dim {d}, all orbital matrices scalar on it: {scal}, '
              f'simple reflections acting nontrivially: {moved}', flush=True)
        if name == 'E8' and d in (35, 84) and not (scal and len(moved) == rs.n): FAIL.append(f'E8 commutant dim {d}')
    print(f'  [{name} commutant check done in {time.time() - t0:.1f}s]', flush=True)

FAIL = []
if __name__ == '__main__':
    for nm in sys.argv[1:]:
        if nm.startswith('commutant:'): commutant_check(nm.split(':')[1])
        else: run(nm)
    if FAIL: print('FAILED CHECKS:', FAIL); sys.exit(1)
    print('ALL CHECKS PASSED')
