#!/usr/bin/env python3
"""Export reflection-permutation tables and search-tree certificates (ArtinRinf/Data/<X>Tree.lean)
for the Franzsen–Howlett route (paper v3, Lemma 4.1): every tuple of reflections with the Coxeter
orders of the simple reflections is conjugate to the simple tuple by an element of rho(W) or
rho(W)pi_0.

The tree is an orbit/stabiliser reduction (pointwise stabilisers via sympy's Schreier–Sims); every
group element used is written as a word in the generators, obtained by lifting to W (signs fixed
along the Dynkin diagram) and the descent algorithm on root images.  Untrusted: Lean re-checks it.
"""
import sys, os
sys.dont_write_bytecode = True  # do not create __pycache__ inside ../code
from collections import deque
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'code', 'indep'))
from sympy.combinatorics import Permutation, PermutationGroup
import rootsys as R
from rootsys import RootSystem

PI0 = {'H3', 'H4', 'F4'}


def compose(p, q): return tuple(p[q[x]] for x in range(len(q)))      # (p*q)(x) = p(q(x))


def inverse(p):
    r = [0] * len(p)
    for i, x in enumerate(p): r[x] = i
    return tuple(r)


def order(p):
    e = tuple(range(len(p))); x = p; k = 1
    while x != e: x = compose(x, p); k += 1
    return k


class Words:
    def __init__(self, rs):
        self.rs = rs; S = rs.S; n = rs.n
        self.S = S; self.n = n
        pos = set(S); dq = deque(S)
        while dq:
            b = dq.popleft()
            for a in S:
                if a == b: continue
                c = R.reflect(a, b)
                if c not in pos: pos.add(c); dq.append(c)
        self.pos = pos
        self.cart = [[R.div(R.mul(R.num(2), R.dot(S[i], S[j])), R.dot(S[i], S[i])) for j in range(n)]
                     for i in range(n)]
        self.edges = [(i, j) for i in range(n) for j in range(n) if i != j and R.dot(S[i], S[j]) != R.ZERO]

    def lift(self, imgs_lines):
        """signed images of the simple roots, from the images of the simple lines"""
        rs = self.rs; n = self.n
        v = [rs.R[l] for l in imgs_lines]
        eps = [None] * n; eps[0] = 1
        changed = True
        while changed:
            changed = False
            for i, j in self.edges:
                if eps[i] is not None and eps[j] is None:
                    want = R.dot(self.S[i], self.S[j]); have = R.dot(v[i], v[j])
                    eps[j] = eps[i] if want == have else -eps[i]
                    assert want == have or want == R.neg(have)
                    changed = True
        return [v[i] if eps[i] == 1 else R.vneg(v[i]) for i in range(n)]

    def descend(self, img):
        img = list(img); rec = []
        while True:
            neg = [i for i in range(self.n) if img[i] not in self.pos]
            if not neg: break
            i = neg[0]; rec.append(i)
            img = [R.vsub(img[j], R.vscale(self.cart[i][j], img[i])) for j in range(self.n)]
        return img, rec

    def word_or_none(self, tup):
        """a word w with wordPerm w (sidx_i) = tup_i, if the simple lines can be sent there by rho(W)"""
        rs = self.rs
        try:
            img = self.lift(list(tup))
        except AssertionError:
            return None
        for sgn in (1, -1):
            start = img if sgn == 1 else [R.vneg(x) for x in img]
            fin, rec = self.descend(start)
            if fin == list(self.S):
                w = list(reversed(rec))
                p = tuple(range(rs.N))
                for i in w: p = compose(p, rs.gens[i])
                if all(p[rs.sidx[i]] == tup[i] for i in range(self.n)):
                    return w
        return None

    def word(self, h):
        """a word w with wordPerm w = h, for h in rho(W) (h a tuple)"""
        rs = self.rs
        img = self.lift([h[s] for s in rs.sidx])
        for sgn in (1, -1):
            start = img if sgn == 1 else [R.vneg(x) for x in img]
            fin, rec = self.descend(start)
            if fin == list(self.S):
                w = list(reversed(rec))
                p = tuple(range(rs.N))
                for i in w: p = compose(p, rs.gens[i])
                assert p == h, 'word does not reproduce the element'
                return w
        raise RuntimeError('element not in rho(W)')


def bt(xs, lo=0, hi=None):
    if hi is None: hi = len(xs)
    if hi - lo == 1: return f'(.leaf ({xs[lo]}))'
    mid = (lo + hi) // 2
    return f'(.node {mid} {bt(xs, lo, mid)} {bt(xs, mid, hi)})'


def main(name):
    rs = RootSystem(name); N = rs.N; n = rs.n
    gens = [tuple(g) for g in rs.gens]
    W = Words(rs)
    G = PermutationGroup([Permutation(list(g)) for g in gens])
    rp = [tuple(rs.perm_of(rs.R[t])) for t in range(N)]
    for i in range(n): assert rp[rs.sidx[i]] == gens[i]
    M = rs.coxeter
    ordc = {}
    def ordt(a, b):
        if (a, b) not in ordc: ordc[(a, b)] = order(compose(rp[a], rp[b]))
        return ordc[(a, b)]
    pi0 = None
    if name in PI0:
        import indep_check
        p0, _ = indep_check.explicit_pi0(name, rs); pi0 = tuple(int(x) for x in p0)
    perm = lambda sp: tuple(sp.array_form) + tuple(range(len(sp.array_form), N))
    nodes = []; child = {}; repf = {}; hw = {}; leaf = {}
    def search(tup, H):
        q = len(nodes); nodes.append(tuple(tup)); k = len(tup)
        if k == n:
            # leaf: find C in G or G pi0 with C(sidx_i) = tup_i
            w = W.word_or_none(list(tup))
            if w is not None:
                leaf[q] = (w, False)
            else:
                assert pi0 is not None, 'leaf not conjugate to the simple tuple'
                a = [pi0[s] for s in rs.sidx]
                g = tuple(range(N)); Hc = G
                for i in range(n):
                    ai = g[a[i]]
                    tr = dict((pt, perm(pp)) for pt, pp in Hc.orbit_transversal(ai, pairs=True))
                    u = tr[tup[i]]
                    g = compose(u, g)
                    Hc = Hc.stabilizer(tup[i])
                assert all(g[a[i]] == tup[i] for i in range(n))
                leaf[q] = (W.word(g), True)
            return q
        cand = [c for c in range(N) if all(ordt(tup[j], c) == M[j][k] for j in range(k))]
        done = {}
        for c in cand:
            if c in done: continue
            tr = dict((pt, perm(pp)) for pt, pp in H.orbit_transversal(c, pairs=True))
            qc = search(tup + [c], H.stabilizer(c))
            for pt, u in tr.items():
                done[pt] = (c, u, qc)
        for c in cand:
            r, u, qc = done[c]
            assert u[r] == c and all(u[p] == p for p in tup)
            child[(q, c)] = qc; repf[(q, c)] = r; hw[(q, c)] = W.word(u) if u != tuple(range(N)) else []
        return q
    search([], G)
    K = len(nodes)
    print(name, 'nodes', K, 'cands', len(child), 'leaves', len(leaf),
          'max word', max([len(w) for w in hw.values()] + [len(w) for w, _ in leaf.values()]), file=sys.stderr)
    L = lambda xs: '[' + ', '.join(map(str, xs)) + ']'
    big = N >= 100
    def tab2(nm, A, Bn, C, rows):
        if big:
            return (f'def {nm} : Fin {A} → Fin {Bn} → {C} := fun i j =>\n  BT.get (BT.get ({bt([bt(r) for r in rows])} : BT (BT ({C}))) i.val) j.val\n')
        return f'def {nm} : Fin {A} → Fin {Bn} → {C} := ![\n  ' + ',\n  '.join('![' + ', '.join(r) + ']' for r in rows) + ']\n'
    out = [f'/-\nGenerated by scripts/export_tree.py -- do not edit.\nType {name}: reflection permutations and a search tree with {K} nodes,\n'
           f'{len(child)} admissible extensions, {len(leaf)} leaves.\n-/',
           'import ArtinRinf.BT\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n',
           f'namespace ArtinRinf.{name}Tree\n\nopen ArtinRinf\n\nnoncomputable section\n',
           '/-- `rpFun t` is the permutation of the reflections induced by conjugation with `t` -/',
           tab2('rpFun', N, N, f'Fin {N}', [list(map(str, r)) for r in rp]),
           f'def K : ℕ := {K}\n',
           f'def node : Fin {K} → List (Fin {N}) := ![' + ', '.join(L(t) for t in nodes) + ']\n',
           f'def root : Fin {K} := 0\n']
    rows_child = [[str(child.get((q, c), 0)) for c in range(N)] for q in range(K)]
    rows_rep = [[str(repf.get((q, c), c)) for c in range(N)] for q in range(K)]
    rows_hw = [[L(hw.get((q, c), [])) for c in range(N)] for q in range(K)]
    out.append(f'def child : Fin {K} → Fin {N} → Fin {K} := ![\n  ' + ',\n  '.join('![' + ', '.join(r) + ']' for r in rows_child) + ']\n')
    out.append(f'def repF : Fin {K} → Fin {N} → Fin {N} := ![\n  ' + ',\n  '.join('![' + ', '.join(r) + ']' for r in rows_rep) + ']\n')
    out.append(f'def hw : Fin {K} → Fin {N} → List (Fin {n}) := ![\n  ' + ',\n  '.join('![' + ', '.join(r) + ']' for r in rows_hw) + ']\n')
    out.append(f'def leafW : Fin {K} → List (Fin {n}) := ![' + ', '.join(L(leaf[q][0]) if q in leaf else '[]' for q in range(K)) + ']\n')
    out.append(f'def leafE : Fin {K} → Bool := ![' + ', '.join(('true' if leaf[q][1] else 'false') if q in leaf else 'false' for q in range(K)) + ']\n')
    out += ['end\n', f'end ArtinRinf.{name}Tree\n']
    open(os.path.join(HERE, '..', 'ArtinRinf', 'Data', f'{name}Tree.lean'), 'w').write('\n'.join(out))


if __name__ == '__main__':
    for nm in sys.argv[1:]:
        main(nm)
