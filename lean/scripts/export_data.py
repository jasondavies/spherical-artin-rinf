#!/usr/bin/env python3
"""Export the finite certificate data for the Lean formalisation.

Uses the exact root systems of ../code/indep/rootsys.py (read-only import; nothing in code/ is
modified) and the explicit outer permutations pi_0 of ../code/indep/indep_check.py.

For a type X it writes ArtinRinf/Data/X.lean containing:
  * gens   : the permutations of the reflections induced by the simple reflections (r -> s r s)
  * sidx   : the simple reflections as points of T
  * orbWord: for each reflection t, a word w and i with w s_i w^-1 = t
  * an orbital certificate (labels, representatives, BFS parent generator, depth)
  * an integer basis of each chosen good constituent U and the scalars mu by which the orbital
    matrices act on it
  * pi_0 (H3, H4, F4) and integer eigenvalue witnesses (words + coefficient vectors)
All of this is re-checked in Lean by `decide`; this script is untrusted.
"""
import sys, os
sys.dont_write_bytecode = True  # do not create __pycache__ inside ../code
import itertools
from collections import deque
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'code', 'indep'))
import numpy as np
from sympy import Matrix, ilcm, igcd
import rootsys as rsm
from rootsys import RootSystem

SPEC = {  # chosen constituent dimensions
    'H3': [4], 'F4': [2, 2], 'H4': [16], 'E6': [15], 'E7': [27], 'E8': [35],
}
OUTER = {'H3': 'stable', 'H4': 'stable', 'F4': 'swap'}


def compose(p, q):  # (p*q)(x) = p(q(x))
    return tuple(p[q[x]] for x in range(len(q)))


def word_perm(gens, w, N):
    x = tuple(range(N))
    for i in w:
        x = compose(x, gens[i])
    return x


def orbitals(gens, N):
    lab = {}
    k = 0
    rep = []
    par = {}
    depth = {}
    for r in range(N):
        for s in range(N):
            if (r, s) in lab:
                continue
            lab[(r, s)] = k; rep.append((r, s)); par[(r, s)] = None; depth[(r, s)] = 0
            dq = deque([(r, s)])
            while dq:
                p = dq.popleft()
                for i, g in enumerate(gens):
                    q = (g[p[0]], g[p[1]])
                    if q not in lab:
                        lab[q] = k; par[q] = i; depth[q] = depth[p] + 1  # g q = p (involution)
                        dq.append(q)
            k += 1
    return k, lab, rep, par, depth


def perm_matrix(p):
    N = len(p); P = np.zeros((N, N), dtype=object)
    for r in range(N): P[p[r], r] = 1          # e_r -> e_{p(r)}
    return P


def int_cols(B):
    cols = []
    for j in range(B.shape[1]):
        c = [B[i, j] for i in range(B.shape[0])]
        den = ilcm(*[Fr(x).denominator for x in c])
        v = [int(Fr(x) * den) for x in c]
        g = 0
        for x in v: g = igcd(g, x)
        v = [x // g for x in v]
        cols.append(v)
    return cols


def nullspace(Mrows):
    M = Matrix(Mrows)
    return M.nullspace()


def constituents(gens, N, k, lab, dims):
    O = []
    for w in range(k):
        A = np.zeros((N, N), dtype=np.int64)
        for (r, s), l in lab.items():
            if l == w: A[r, s] = 1
        O.append(A)
    rng = np.random.default_rng(7)
    c = rng.integers(1, 50, size=k)
    X = sum(int(ci) * a for ci, a in zip(c, O)); X = X + X.T
    ev = np.linalg.eigvalsh(X.astype(float))
    cands = sorted(set(int(round(x)) for x in ev if abs(x - round(x)) < 1e-6))
    found = []
    for lam in cands:
        mult = int(np.sum(np.abs(ev - lam) < 1e-6))
        if mult not in dims: continue
        ns = nullspace((X - lam * np.eye(N, dtype=np.int64)).tolist())
        if len(ns) != mult: continue
        B = Matrix.hstack(*ns)
        cols = int_cols(B)
        Bi = np.array(cols, dtype=object).T            # N x d
        mus = []
        ok = True
        for A in O:
            AB = A.astype(object).dot(Bi)
            j0 = next(i for i in range(N) if Bi[i, 0] != 0)
            mu = Fr(int(AB[j0, 0]), int(Bi[j0, 0]))
            if mu.denominator != 1 or not all(AB[i, j] == mu * Bi[i, j] for i in range(N) for j in range(Bi.shape[1])):
                ok = False; break
            mus.append(int(mu))
        if ok:
            found.append((lam, cols, mus))
    return O, found


def solve_coeffs(Bi, v):
    """coefficients c (integers, after scaling v if necessary is NOT allowed) with Bi c = v"""
    M = Matrix(Bi.tolist())
    sol, params = M.gauss_jordan_solve(Matrix(v))
    assert len(params) == 0
    c = [Fr(int(x.p), int(x.q)) for x in sol]
    assert all(x.denominator == 1 for x in c), c
    return [int(x) for x in c]


def eig_coeffs(Q, Bi, eps):
    """integer c != 0 with P_Q Bi c = eps Bi c, or None"""
    PQ = perm_matrix(Q)
    Mx = PQ.dot(Bi) - eps * Bi
    ns = nullspace(Mx.tolist())
    if not ns: return None
    v = ns[0]
    den = ilcm(*[Fr(int(x.p), int(x.q)).denominator for x in v])
    c = [int(Fr(int(x.p), int(x.q)) * den) for x in v]
    return c


def group_words(gens, N, limit=None):
    """BFS: element (perm tuple) -> shortest word"""
    e = tuple(range(N))
    words = {e: []}
    dq = deque([e])
    while dq:
        x = dq.popleft()
        for i, g in enumerate(gens):
            y = compose(x, g)
            if y not in words:
                words[y] = words[x] + [i]
                dq.append(y)
                if limit and len(words) >= limit: return words
    return words


def lean_fin_list(xs):
    return '![' + ', '.join(str(x) for x in xs) + ']'


def lean_int_list(xs):
    return '![' + ', '.join(str(x) if x >= 0 else f'({x})' for x in xs) + ']'


def lean_list(xs):
    return '[' + ', '.join(str(x) for x in xs) + ']'


def bt(xs, lo=0, hi=None):
    """balanced BT literal for the list of (already formatted) entries xs"""
    if hi is None: hi = len(xs)
    if hi - lo == 1: return f'(.leaf ({xs[lo]}))'
    mid = (lo + hi) // 2
    return f'(.node {mid} {bt(xs, lo, mid)} {bt(xs, mid, hi)})'


def table1(name, A, B, xs, use_bt):
    """def name : Fin A → B := ... for formatted entries xs"""
    if use_bt:
        return f'def {name} : Fin {A} → {B} := fun i => BT.get ({bt(xs)} : BT ({B})) i.val\n'
    return f'def {name} : Fin {A} → {B} := ![' + ', '.join(xs) + ']\n'


def table2(name, A, B, C, rows, use_bt):
    """def name : Fin A → Fin B → C := ... for rows of formatted entries"""
    if use_bt:
        inner = [bt(r) for r in rows]
        return (f'def {name} : Fin {A} → Fin {B} → {C} := fun i j =>\n  BT.get (BT.get ({bt(inner)} : BT (BT ({C}))) i.val) j.val\n')
    return f'def {name} : Fin {A} → Fin {B} → {C} := ![\n  ' + ',\n  '.join('![' + ', '.join(r) + ']' for r in rows) + ']\n'


def ints(xs): return [str(x) if x >= 0 else f'({x})' for x in xs]


def main(name):
    rs = RootSystem(name)
    N = rs.N; n = rs.n
    gens = [tuple(g) for g in rs.gens]
    for g in gens: assert compose(g, g) == tuple(range(N))
    sidx = rs.sidx
    k, lab, rep, par, depth = orbitals(gens, N)
    # orbit words
    orbw = {}
    dq = deque()
    for i in range(n):
        if sidx[i] not in orbw:
            orbw[sidx[i]] = ([], i); dq.append(sidx[i])
    while dq:
        t = dq.popleft()
        for j, g in enumerate(gens):
            u = g[t]
            if u not in orbw:
                orbw[u] = ([j] + orbw[t][0], orbw[t][1]); dq.append(u)
    assert len(orbw) == N
    O, found = constituents(gens, N, k, lab, SPEC[name])
    print(name, 'N', N, 'orbitals', k, 'constituents', [(l, len(c)) for l, c, _ in found], file=sys.stderr)
    out = []
    use_bt = N >= 100
    P = f'ArtinRinf.{name}Data'
    out.append(f'/-\nGenerated by scripts/export_data.py from code/indep/rootsys.py -- do not edit.\n'
               f'Type {name}: |T| = {N} reflections, {k} orbitals on T x T.\n-/\nimport ArtinRinf.BT\n\n'
               f'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace {P}\n\nopen ArtinRinf\n\nnoncomputable section\n')
    out.append(f'/-- generator permutations of the {N} reflections -/')
    out.append(table2('gensFun', n, N, f'Fin {N}', [list(map(str, g)) for g in gens], use_bt))
    out.append(f'def sidx : Fin {n} → Fin {N} := {lean_fin_list(sidx)}\n')
    out.append(table1('orbWord', N, f'List (Fin {n}) × Fin {n}', [f'({lean_list(orbw[t][0])}, {orbw[t][1]})' for t in range(N)], use_bt))
    out.append(table2('lab', N, N, f'Fin {k}', [[str(lab[(r, s)]) for s in range(N)] for r in range(N)], use_bt))
    out.append(f'def rep : Fin {k} → Fin {N} × Fin {N} := ![' + ', '.join(f'({a}, {b})' for a, b in rep) + ']\n')
    def popt(x): return 'none' if x is None else f'some {x}'
    out.append(table2('par', N, N, f'Option (Fin {n})', [[popt(par[(r, s)]) for s in range(N)] for r in range(N)], use_bt))
    out.append(table2('depth', N, N, 'ℕ', [[str(depth[(r, s)]) for s in range(N)] for r in range(N)], use_bt))
    Bs = []
    for idx, (lam, cols, mus) in enumerate(found):
        d = len(cols)
        Bi = np.array(cols, dtype=object).T
        Bs.append(Bi)
        out.append(f'/-- integer basis of a good constituent (eigenvalue {lam} of a commutant element), dim {d} -/')
        out.append(table2(f'U{idx}', d, N, 'ℤ', [ints(c) for c in cols], use_bt))
        out.append(f'def mu{idx} : Fin {k} → ℤ := {lean_int_list(mus)}\n')
    # inner witnesses on U0: eps=+1 with h=1, eps=-1 with h = a simple reflection
    words = None
    def wit(Q, Bi):
        return eig_coeffs(Q, Bi, 1), eig_coeffs(Q, Bi, -1)
    e = tuple(range(N))
    c_plus = [1] + [0] * (Bs[0].shape[1] - 1)
    i_moved = None
    for i in range(n):
        c = eig_coeffs(gens[i], Bs[0], -1)
        if c is not None: i_moved = i; c_minus = c; break
    assert i_moved is not None
    out.append(f'/-- inner case: `ρ(s_{i_moved})` has eigenvalue -1 on U0 -/')
    out.append(f'def innerMinusGen : Fin {n} := {i_moved}\n')
    out.append(f'def innerPlusC : Fin {Bs[0].shape[1]} → ℤ := {lean_int_list(c_plus)}\n')
    out.append(f'def innerMinusC : Fin {Bs[0].shape[1]} → ℤ := {lean_int_list(c_minus)}\n')
    if name in OUTER:
        import indep_check
        pi0, desc = indep_check.explicit_pi0(name, rs)
        pi0 = tuple(int(x) for x in pi0)
        out.append(f'/-- the outer permutation pi_0 ({desc}) -/')
        out.append(table1('pi0Fun', N, f'Fin {N}', list(map(str, pi0)), use_bt))
        words = group_words(gens, N)
        pinv = [0] * N
        for r in range(N): pinv[pi0[r]] = r
        pinv = tuple(pinv)
        conjw = []
        for g in gens:
            c = compose(compose(pi0, g), pinv)
            assert c in words, 'pi0 does not normalise'
            conjw.append(words[c])
        out.append(f'/-- words for `π₀ ρ(s_i) π₀⁻¹ ∈ ρ(W)` -/')
        out.append(f'def pi0ConjWord : Fin {n} → List (Fin {n}) := ![' + ', '.join(lean_list(w) for w in conjw) + ']\n')
        if OUTER[name] == 'stable':
            res = {}
            for eps in (1, -1):
                for x, w in sorted(words.items(), key=lambda kv: len(kv[1])):
                    Q = compose(x, pi0)
                    c = eig_coeffs(Q, Bs[0], eps)
                    if c is not None: res[eps] = (w, c); break
            out.append(f'def outerPlusWord : List (Fin {n}) := {lean_list(res[1][0])}\n')
            out.append(f'def outerPlusC : Fin {Bs[0].shape[1]} → ℤ := {lean_int_list(res[1][1])}\n')
            out.append(f'def outerMinusWord : List (Fin {n}) := {lean_list(res[-1][0])}\n')
            out.append(f'def outerMinusC : Fin {Bs[0].shape[1]} → ℤ := {lean_int_list(res[-1][1])}\n')
        else:
            res = {}
            for eps in (1, -1):
                for x, w in sorted(words.items(), key=lambda kv: len(kv[1])):
                    Q = compose(x, pi0)
                    Q2 = compose(Q, Q)
                    c = eig_coeffs(Q2, Bs[0], eps)
                    if c is None: continue
                    v = Bs[0].dot(np.array(c, dtype=object))
                    Qv = perm_matrix(Q).dot(v)
                    try:
                        c2 = solve_coeffs(Bs[1], list(Qv))
                    except Exception:
                        continue
                    res[eps] = (w, c, c2); break
            for eps, tag in ((1, 'Plus'), (-1, 'Minus')):
                w, c, c2 = res[eps]
                out.append(f'def outer{tag}Word : List (Fin {n}) := {lean_list(w)}\n')
                out.append(f'def outer{tag}C : Fin {Bs[0].shape[1]} → ℤ := {lean_int_list(c)}\n')
                out.append(f'def outer{tag}C2 : Fin {Bs[1].shape[1]} → ℤ := {lean_int_list(c2)}\n')
    out.append(f'end\n\nend {P}\n')
    path = os.path.join(HERE, '..', 'ArtinRinf', 'Data', f'{name}.lean')
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, 'w').write('\n'.join(out))
    print('wrote', path, file=sys.stderr)


if __name__ == '__main__':
    for nm in sys.argv[1:]:
        main(nm)
