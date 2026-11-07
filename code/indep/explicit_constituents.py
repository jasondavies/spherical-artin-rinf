"""Exact checks of the EXPLICIT good constituents and witnesses used in the revised paper (Sections 4-5).

Each part constructs the constituent by hand-style recipe (strongly regular graph eigenspace, frame
functions, matrix coefficients, weight vectors) and verifies by exact arithmetic that it is a good
constituent (W-invariant, character norms 1 and multiplicity 1, or commutant-scalar), that it has the
expected dimension, and that the stated witnesses exist.  It also checks the two errors pointed out by the
external review (D4 reducibility of U^-, Bourbaki indexing of E8 simple roots).

Usage:  python3 explicit_constituents.py [srg] [h3] [f4] [h4] [d4] [bd] [bourbaki]   (default: all)
Imports only rootsys.py / permgroup.py / indep_check.py (helpers) from this directory.
"""
import sys, itertools, time
import numpy as np
from fractions import Fraction as Fr
import rootsys as R
from rootsys import RootSystem, num, mul, add, sub, neg, galois, dot, canon, vscale
from permgroup import enumerate_group, inverse, order, generated_order
from indep_check import nullspace_basis, int_basis, character, nullity, permmat, explicit_pi0, dm

def say(*a): print(*a, flush=True)

def lines_dot(rs):
    """matrix of inner products between the canonical roots of the lines (exact, as tuples)"""
    N = rs.N
    return [[dot(rs.R[a], rs.R[b]) for b in range(N)] for a in range(N)]

def is_zero(x): return x[0] == 0 and x[1] == 0

def good_by_characters(B, E, fixv):
    chi = character(B, E); G = len(E)
    return Fr(int((chi * chi).sum()), G), Fr(int((chi * fixv).sum()), G), chi

def span_contains(B, V):
    """exact test: columns of V lie in the column space of B"""
    return dm(np.hstack([B, V]).T.tolist()).rank() == dm(B.T.tolist()).rank()

def eig_dims(P, B):
    """exact dimensions of the +1 and -1 eigenspaces of the permutation matrix P on span(B) (P preserves span B)"""
    I = np.eye(P.shape[0], dtype=np.int64)
    return nullity((P - I) @ B), nullity((P + I) @ B)

def frames(rs, D, subset):
    """maximal sets of mutually orthogonal lines inside `subset`, which must partition it"""
    sub_ = list(subset); out = []; used = set()
    for a in sub_:
        if a in used: continue
        F = [a] + [b for b in sub_ if b != a and is_zero(D[a][b])]
        # check mutual orthogonality
        assert all(is_zero(D[x][y]) for x in F for y in F if x != y), 'not a frame partition'
        out.append(sorted(F)); used |= set(F)
    return out

def frame_module(N, frs):
    """integer basis of {functions constant on frames, total sum 0}"""
    cols = []
    for F in frs[1:]:
        v = np.zeros(N, dtype=np.int64); v[F] = 1; v[frs[0]] = -1; cols.append(v)
    return np.array(cols).T

def action_on_blocks(p, blocks):
    idx = {x: i for i, B in enumerate(blocks) for x in B}
    img = []
    for B in blocks:
        t = {idx[p[x]] for x in B}; assert len(t) == 1; img.append(t.pop())
    return tuple(img)

# ----------------------------------------------------------------------------------------------
def part_bourbaki():
    say('===== Bourbaki indexing of the E-type simple roots (review point 1b)')
    S = R.simple_roots('E8')
    def fmt(v): return '(' + ','.join(str(x[0]) for x in v) + ')'
    for k, v in enumerate(S, 1):
        say(f'  alpha_{k} = {fmt(v)}')
    ok = all(tuple(x[0] for x in S[k - 1]) == tuple((1 if t == k - 2 else -1 if t == k - 3 else 0) for t in range(8))
             for k in range(3, 9))
    say(f'  alpha_k = e_(k-1) - e_(k-2) for 3<=k<=8 (1-based coordinates e_1..e_8): {ok}')
    say('  E7 uses alpha_1..alpha_7 and E6 uses alpha_1..alpha_6, all inside R^8.')

def part_srg():
    for name, exp in [('E6', (36, 15, 6, 6)), ('E7', (63, 30, 13, 15)), ('E8', (120, 63, 30, 36))]:
        t0 = time.time(); rs = RootSystem(name); N = rs.N; D = lines_dot(rs)
        A = np.array([[1 if (a != b and is_zero(D[a][b])) else 0 for b in range(N)] for a in range(N)], dtype=np.int64)
        k = set(A.sum(1).tolist())
        lam = {int(A[a] @ A[b]) for a in range(N) for b in range(N) if A[a, b]}
        mu = {int(A[a] @ A[b]) for a in range(N) for b in range(N) if a != b and not A[a, b]}
        params = (N, k.pop() if len(k) == 1 else k, lam.pop() if len(lam) == 1 else lam, mu.pop() if len(mu) == 1 else mu)
        # orbitals of rho(W) on lines x lines
        par = list(range(N * N))
        def find(x):
            while par[x] != x: par[x] = par[par[x]]; x = par[x]
            return x
        for g in rs.gens:
            for a in range(N):
                for b in range(N):
                    x, y = find(a * N + b), find(g[a] * N + g[b])
                    if x != y: par[x] = y
        norb = len({find(i) for i in range(N * N)})
        # spectrum
        v, kk, l, m = exp
        disc = (l - m) ** 2 + 4 * (kk - m); r = ((l - m) + int(round(disc ** .5))) // 2; s = ((l - m) - int(round(disc ** .5))) // 2
        I = np.eye(N, dtype=np.int64)
        mr, ms, mk = nullity(A - r * I), nullity(A - s * I), nullity(A - kk * I)
        # perpendicular subsystems (root counts)
        roots = rs.roots
        a0 = roots[0]
        perp1 = [x for x in roots if is_zero(dot(x, a0))]
        g0 = next(x for x in perp1)
        perp2 = [x for x in perp1 if is_zero(dot(x, g0))]
        b0 = next(x for x in roots if dot(x, a0) == num(1))
        perpA2 = [x for x in roots if is_zero(dot(x, a0)) and is_zero(dot(x, b0))]
        nonorth1 = sum(1 for x in roots if dot(x, a0) == num(1))
        say(f'===== {name}: SRG parameters {params} (expected {exp}): {params == exp}; orbitals on lines x lines: {norb}')
        say(f'  eigenvalues of the orthogonality graph: {kk}^{mk}, {r}^{mr}, {s}^{ms}  (dims sum {mk + mr + ms} = {N})')
        def rk(L): return int(np.linalg.matrix_rank(np.array([[R.tofloat(c) for c in x] for x in L]))) if L else 0
        say(f'  roots: |Phi| = {len(roots)}, perp to a root: {len(perp1)} (rank {rk(perp1)}), perp to two orthogonal roots: '
            f'{len(perp2)} (rank {rk(perp2)}), perp to an A2: {len(perpA2)} (rank {rk(perpA2)}), roots with (alpha,beta)=1: {nonorth1}'
            f'   [{time.time() - t0:.1f}s]')
        # good constituents: commutant = span{I, A, J}; eigenspaces of A for r, s are commutant-scalar
        Br = int_basis(nullspace_basis(A - r * I)); Bs = int_basis(nullspace_basis(A - s * I))
        J = np.ones((N, N), dtype=np.int64)
        scal = all(np.all(J @ B == 0) for B in (Br, Bs))
        moved = [all(not np.array_equal(permmat(np.array(g)) @ B, B) for g in rs.gens) for B in (Br, Bs)]
        say(f'  J kills both eigenspaces (so span{{I,A,J}} acts by scalars): {scal}; every simple reflection moves them: {moved}')

def part_h3():
    rs = RootSystem('H3'); N = rs.N; D = lines_dot(rs)
    E, index = enumerate_group(rs.gens); fixv = (E == np.arange(N, dtype=E.dtype)).sum(1).astype(np.int64)
    frs = frames(rs, D, range(N))
    B = frame_module(N, frs)
    inv = all(len({action_on_blocks(g, frs)}) == 1 for g in rs.gens)
    n1, n2, chi = good_by_characters(B, E, fixv)
    pi0, _ = explicit_pi0('H3', rs); pi0 = pi0.astype(np.int64)
    img = action_on_blocks(pi0, frs)
    cyc = sorted(len(c) for c in cycles(img))
    say(f'===== H3: {len(frs)} frames (orthogonal triples) of sizes {[len(F) for F in frs]} partition the 15 lines')
    say(f'  frame module: dim {B.shape[1]}, W permutes frames: {inv}, <chi,chi> = {n1}, <chi,perm> = {n2}; '
        f'image of W on the 5 frames has order {generated_order([action_on_blocks(g, frs) for g in rs.gens])}')
    say(f'  pi_0 acts on the 5 frames with cycle type {cyc}; eigenspace dims of pi_0 on U (+1,-1): {eig_dims(permmat(pi0), B)}')

def cycles(p):
    seen = set(); out = []
    for i in range(len(p)):
        if i in seen: continue
        c = []; j = i
        while j not in seen: seen.add(j); c.append(j); j = p[j]
        out.append(c)
    return out

def part_f4():
    rs = RootSystem('F4'); N = rs.N; D = lines_dot(rs)
    E, index = enumerate_group(rs.gens); fixv = (E == np.arange(N, dtype=E.dtype)).sum(1).astype(np.int64)
    norm = [dot(rs.R[a], rs.R[a]) for a in range(N)]
    long_ = [a for a in range(N) if norm[a] == num(2)]; short = [a for a in range(N) if norm[a] == num(1)]
    FL, FS = frames(rs, D, long_), frames(rs, D, short)
    BL, BS = frame_module(N, FL), frame_module(N, FS)
    say(f'===== F4: long lines {len(long_)} -> frames {[len(F) for F in FL]}; short lines {len(short)} -> frames {[len(F) for F in FS]}')
    for nm, Bx, Fx in (('U_long', BL, FL), ('U_short', BS, FS)):
        n1, n2, _ = good_by_characters(Bx, E, fixv)
        moved = [i for i in range(4) if not np.array_equal(permmat(np.array(rs.gens[i])) @ Bx, Bx)]
        imgord = generated_order([action_on_blocks(g, Fx) for g in rs.gens])
        say(f'  {nm}: dim {Bx.shape[1]}, <chi,chi> = {n1}, <chi,perm> = {n2}, simple reflections acting nontrivially: {moved} '
            f'(alpha_1, alpha_2 long), image of W on its 3 frames has order {imgord}')
    pi0, _ = explicit_pi0('F4', rs); pi0 = pi0.astype(np.int64); P0 = permmat(pi0)
    sw = span_contains(BS, P0 @ BL) and span_contains(BL, P0 @ BS)
    say(f'  pi_0 maps U_long onto U_short and back: {sw}; pi_0^2 = 1: {np.array_equal(pi0[pi0], np.arange(N))}')
    s1 = np.array(rs.gens[0], dtype=np.int64)
    q = s1[pi0]; q2 = q[q]
    say(f'  (s_1 pi_0)^2 = s_1 * (pi_0 s_1 pi_0): eigenspace dims (+1,-1) on U_short: {eig_dims(permmat(q2), BS)}; '
        f'pi_0^2 on U_short: {eig_dims(permmat(pi0[pi0]), BS)}')

def qmul(a, b):
    a0, a1, a2, a3 = a; b0, b1, b2, b3 = b; m = mul
    return (sub(sub(sub(m(a0, b0), m(a1, b1)), m(a2, b2)), m(a3, b3)),
            sub(add(add(m(a0, b1), m(a1, b0)), m(a2, b3)), m(a3, b2)),
            add(sub(add(m(a0, b2), m(a2, b0)), m(a1, b3)), m(a3, b1)),
            sub(add(add(m(a0, b3), m(a3, b0)), m(a1, b2)), m(a2, b1)))
def qconj(a): return (a[0], neg(a[1]), neg(a[2]), neg(a[3]))

def part_h4():
    t0 = time.time()
    rs = RootSystem('H4'); N = rs.N
    half = num(Fr(1, 2))
    unit = lambda r: tuple(mul(half, x) for x in r)
    I_ = [unit(r) for r in rs.roots]; Iset = set(I_)
    closed = all(qmul(a, b) in Iset for a in I_ for b in I_)
    one = (num(1), num(0), num(0), num(0))
    say(f'===== H4: the 120 roots/2 form a group under quaternion multiplication (icosians): {closed}; contains 1: {one in Iset}')
    # lines <-> K = I/{+-1}
    line_of = {}
    for a in range(N):
        u = unit(rs.R[a]); line_of[u] = a; line_of[tuple(neg(x) for x in u)] = a
    rep = [unit(rs.R[a]) for a in range(N)]
    Lmul = lambda a, b: line_of[qmul(rep[a], rep[b])]
    Linv = lambda a: line_of[qconj(rep[a])]
    # reflection s_r acts on lines by x -> r xbar r
    ok = True
    for r in range(N):
        p = rs.perm_of(rs.R[r])
        for x in range(N):
            if p[x] != line_of[qmul(qmul(rep[r], qconj(rep[x])), rep[r])]: ok = False
    say(f'  reflection s_r acts on lines as x -> r x^(-1) r: {ok}')
    E, index = enumerate_group(rs.gens); fixv = (E == np.arange(N, dtype=E.dtype)).sum(1).astype(np.int64)
    left = [tuple(Lmul(a, x) for x in range(N)) for a in range(N)]
    right = [tuple(Lmul(x, a) for x in range(N)) for a in range(N)]
    inv = tuple(Linv(x) for x in range(N))
    gens2 = left + right + [inv]
    o2 = generated_order(gens2)
    contained = all(np.asarray(g, dtype=E.dtype).tobytes() in index for g in gens2)
    say(f'  <left mult, right mult, inversion> has order {o2}; equals rho(W) (|rho(W)| = {len(E)}, contained: {contained}): '
        f'{o2 == len(E) and contained}')
    # K = A5: involutions and Klein four-subgroups
    e = line_of[one]
    invols = [x for x in range(N) if x != e and Lmul(x, x) == e]
    V4 = []
    for x in invols:
        S = sorted({x} | {y for y in invols if y != x and Lmul(x, y) == Lmul(y, x)})
        if S not in V4: V4.append(S)
    say(f'  K has {len(invols)} involutions in {len(V4)} Klein four-subgroups (sizes {[len(S) for S in V4]})')
    def act(x, S): return sorted(Lmul(Lmul(x, s), Linv(x)) for s in S)
    perm5 = [tuple(V4.index(act(x, S)) for S in V4) for x in range(N)]
    # matrix coefficients c_ab(x) = [x V_b x^-1 = V_a]; U = span{c_ab - 1/5}
    cols = []
    for a in range(5):
        for b in range(5):
            v = np.array([5 * (1 if perm5[x][b] == a else 0) - 1 for x in range(N)], dtype=np.int64); cols.append(v)
    M = np.array(cols).T
    from sympy import Matrix
    Bm = Matrix(M.tolist()).columnspace()
    B = np.array([[int(x) for x in c] for c in Bm], dtype=np.int64).T
    B = int_basis(Matrix(B.tolist()))
    n1, n2, _ = good_by_characters(B, E, fixv)
    invU = all(span_contains(B, permmat(np.array(g)) @ B) for g in rs.gens)
    say(f'  matrix-coefficient space of the 4-dim representation: dim {B.shape[1]}, W-invariant {invU}, '
        f'<chi,chi> = {n1}, <chi,perm> = {n2}')
    # outer: semilinear ring automorphism Psi = P o sigma, P a rotation of (i,j,k) by a signed permutation
    found = None
    for p in itertools.permutations(range(3)):
        for sg in itertools.product((1, -1), repeat=3):
            def Psi(x, p=p, sg=sg):
                y = [galois(c) for c in x]; z = [y[0], None, None, None]
                for t in range(3): z[1 + p[t]] = mul(num(sg[t]), y[1 + t])
                return tuple(z)
            if not all(Psi(x) in Iset for x in I_): continue
            if all(Psi(qmul(a, b)) == qmul(Psi(a), Psi(b)) for a in I_[:40] for b in I_):
                found = (p, sg, Psi); break
        if found: break
    p, sg, Psi = found
    piP = np.array([line_of[Psi(rep[x])] for x in range(N)], dtype=np.int64)
    # Psi multiplicative on all of I?
    mult = all(Psi(qmul(a, b)) == qmul(Psi(a), Psi(b)) for a in I_ for b in I_)
    # normalises rho(W) and is outer
    gens = [np.asarray(g, dtype=np.int64) for g in rs.gens]; pinv = inverse(piP)
    conj = [piP[g][pinv] for g in gens]
    norm_ok = all(c.astype(E.dtype).tobytes() in index for c in conj)
    inner = False
    for h in E.astype(np.int64):
        hi = inverse(h)
        if all(np.array_equal(h[g][hi], c) for g, c in zip(gens, conj)): inner = True; break
    say(f'  Psi = (signed permutation {p},{sg} of i,j,k) o Galois: ring automorphism of the icosians: {mult}; '
        f'induced permutation normalises rho(W): {norm_ok}; outer: {not inner}')
    # compose with an inner automorphism x -> a x a^-1 (an element of rho(W)) so that the result acts on the
    # five Klein four-subgroups as a transposition; it is then an involution
    best = None
    for a in range(N):
        q = np.array([Lmul(Lmul(a, piP[x]), Linv(a)) for x in range(N)], dtype=np.int64)
        on5 = tuple(V4.index(sorted(q[s_] for s_ in S)) for S in V4)
        if sorted(len(c) for c in cycles(on5)) == [1, 1, 1, 2]: best = (a, q, on5); break
    a, q, on5 = best
    conj_in_W = np.asarray([Lmul(Lmul(a, x), Linv(a)) for x in range(N)], dtype=E.dtype).tobytes() in index
    say(f'  pi_Psi itself has order {order(piP)}; x -> a Psi(x) a^-1 (a = line {a}; conjugation by a lies in rho(W): {conj_in_W}) '
        f'acts on the 5 Klein subgroups as {on5}, has order {order(q)}, eigenspace dims (+1,-1) on U: {eig_dims(permmat(q), B)}')
    pi0, _ = explicit_pi0('H4', rs); pi0 = pi0.astype(np.int64)
    q = pi0[inverse(piP)]
    say(f'  pi_0 pi_Psi^(-1) lies in rho(W) (same outer class): {q.astype(E.dtype).tobytes() in index}   [{time.time() - t0:.1f}s]')

def lin_perm(rs, M):
    """permutation of lines induced by an integer matrix M (rational root system)"""
    M = [[int(x) for x in row] for row in np.asarray(M)]
    return np.array(rs.perm_of_map(lambda v: tuple(num(sum(Fr(M[i][j]) * v[j][0] for j in range(len(v)))) for i in range(len(v)))),
                    dtype=np.int64)

def part_d4():
    rs = RootSystem('D4'); N = rs.N; D = lines_dot(rs)
    E, index = enumerate_group(rs.gens); fixv = (E == np.arange(N, dtype=E.dtype)).sum(1).astype(np.int64)
    n = 4
    def L(v): return rs.lidx[canon(tuple(num(x) for x in v))]
    pairs = list(itertools.combinations(range(n), 2))
    def u(i, j):
        v = np.zeros(N, dtype=np.int64)
        a = [0] * n; a[i] = 1; a[j] = 1; v[L(a)] += 1
        b = [0] * n; b[i] = 1; b[j] = -1; v[L(b)] -= 1
        return v
    Um = np.array([u(i, j) for i, j in pairs]).T
    # J: u_ij -> u_kl
    comp = {p: tuple(sorted(set(range(n)) - set(p))) for p in pairs}
    Jm = np.zeros((6, 6), dtype=np.int64)
    for c, p in enumerate(pairs): Jm[pairs.index(comp[p]), c] = 1
    commute = True
    for g in rs.gens:
        PU = permmat(np.array(g)) @ Um
        # coordinates in the basis u_ij (exact: solve via least squares on integer data then verify)
        X = np.linalg.lstsq(Um.astype(float), PU.astype(float), rcond=None)[0]; Xr = np.rint(X).astype(np.int64)
        assert np.array_equal(Um @ Xr, PU)
        if not np.array_equal(Xr @ Jm, Jm @ Xr): commute = False
    Vp = np.array([u(*p) + u(*comp[p]) for p in pairs[:3]]).T; Vm = np.array([u(*p) - u(*comp[p]) for p in pairs[:3]]).T
    say(f'===== D4: U^- = span(u_ij) has dim {np.linalg.matrix_rank(Um.astype(float))}; '
        f'J: u_ij -> u_kl commutes with W(D4) on U^-: {commute}  (review point 1a)')
    for nm, V in (('J=+1', Vp), ('J=-1', Vm)):
        n1, n2, _ = good_by_characters(V, E, fixv)
        say(f'  {nm} eigenspace of J in U^-: dim {np.linalg.matrix_rank(V.astype(float))}, <chi,chi> = {n1}, <chi,perm> = {n2}')
    FR = frames(rs, D, range(N))
    Bf = frame_module(N, FR)
    n1, n2, _ = good_by_characters(Bf, E, fixv)
    img = generated_order([action_on_blocks(g, FR) for g in rs.gens])
    say(f'  frames: {len(FR)} of sizes {[len(F) for F in FR]}; frame module dim {Bf.shape[1]}, <chi,chi> = {n1}, '
        f'<chi,perm> = {n2}; image of W on frames has order {img}')
    # diagram automorphisms (S3) as isometries permuting the simple roots; witnesses on frame module
    S = [[int(x[0]) for x in a] for a in R.simple_roots('D4')]   # alpha_1..alpha_4; alpha_2 is the centre
    Sm = np.array(S, dtype=float).T
    ok_all = True
    for perm in itertools.permutations([0, 2, 3]):
        gam = {1: 1}; gam.update({a: b for a, b in zip([0, 2, 3], perm)})
        Tm = np.array([S[gam[i]] for i in range(4)], dtype=float).T @ np.linalg.inv(Sm)
        Mi = np.rint(Tm * 2) / 2
        def T(v, Mi=Mi): return tuple(num(Fr(sum(Fr(Mi[i][j]).limit_denominator(4) * v[j][0] for j in range(4)))) for i in range(4))
        pi = np.array(rs.perm_of_map(T), dtype=np.int64)
        found = {}
        for x in range(len(E)):
            q = E[x].astype(np.int64)[pi]
            for eps in (1, -1):
                if eps not in found and nullity((permmat(q) - eps * np.eye(N, dtype=np.int64)) @ Bf) > 0: found[eps] = x
            if len(found) == 2: break
        ok_all &= len(found) == 2
        say(f'  diagram automorphism {gam}: pi permutes frames {action_on_blocks(pi, FR)}; witnesses for +1,-1 on frame module: {sorted(found)}')
    say(f'  all six triality classes have both witnesses: {ok_all}')

def part_bd():
    for name in ['B3', 'B4', 'B5', 'B6', 'D4', 'D5', 'D6', 'D7']:
        t0 = time.time()
        rs = RootSystem(name); N = rs.N; n = int(name[1:])
        E, index = enumerate_group(rs.gens); fixv = (E == np.arange(N, dtype=E.dtype)).sum(1).astype(np.int64)
        def L(v): return rs.lidx[canon(tuple(num(x) for x in v))]
        pairs = list(itertools.combinations(range(n), 2))
        cols = []
        for i, j in pairs:
            v = np.zeros(N, dtype=np.int64)
            a = [0] * n; a[i] = 1; a[j] = 1; v[L(a)] += 1
            b = [0] * n; b[i] = 1; b[j] = -1; v[L(b)] -= 1
            cols.append(v)
        Um = np.array(cols).T
        # sign group (even signs for D): weights of u_ij
        signs = [s for s in itertools.product((1, -1), repeat=n) if name[0] == 'B' or s.count(-1) % 2 == 0]
        weights = []
        for c, (i, j) in enumerate(pairs):
            w = []
            for s in signs:
                p = lin_perm(rs, np.diag(s))
                img = permmat(p) @ Um[:, c]
                if np.array_equal(img, Um[:, c]): w.append(1)
                elif np.array_equal(img, -Um[:, c]): w.append(-1)
                else: raise AssertionError('u_ij not a weight vector')
            weights.append(tuple(w))
        distinct = len(set(weights)) == len(weights); nontriv = all(any(x == -1 for x in w) for w in weights)
        # sign-fixed vectors: e_[ei+ej]+e_[ei-ej] and short roots are fixed by all signs
        fixed_ok = True
        for i, j in pairs:
            v = np.zeros(N, dtype=np.int64); a = [0] * n; a[i] = 1; a[j] = 1; v[L(a)] += 1; b = [0] * n; b[i] = 1; b[j] = -1; v[L(b)] += 1
            fixed_ok &= all(np.array_equal(permmat(lin_perm(rs, np.diag(s))) @ v, v) for s in signs)
        n1, n2, _ = good_by_characters(Um, E, fixv)
        extra = ''
        if name[0] == 'D':
            neg_n = np.eye(n, dtype=int); neg_n[n - 1, n - 1] = -1
            extra = f'; negate-e_n eigenspace dims on U^- (+1,-1): {eig_dims(permmat(lin_perm(rs, neg_n)), Um)}'
        say(f'===== {name}: U^- dim {Um.shape[1]}; weights chi_ij pairwise distinct: {distinct}, nontrivial: {nontriv}; '
            f'sign-fixed vectors fixed: {fixed_ok}; <chi,chi> = {n1}, <chi,perm> = {n2}{extra}   [{time.time() - t0:.1f}s]')

PARTS = {'bourbaki': part_bourbaki, 'srg': part_srg, 'h3': part_h3, 'f4': part_f4, 'h4': part_h4, 'd4': part_d4, 'bd': part_bd}
if __name__ == '__main__':
    for p in (sys.argv[1:] or list(PARTS)): PARTS[p]()
