"""Independent, exact construction of the finite root systems used in the paper.

Written from scratch (does not import any module of the original code).
Numbers live in Q(phi), phi = (1+sqrt5)/2, stored as pairs (a, b) of Fractions meaning a + b*phi.
For the crystallographic types all b are 0.

Provides, for a type name in {H3, H4, F4, E6, E7, E8, D5}:
  roots      : list of root vectors (tuples of Q(phi) numbers), closed under the reflection group
  simple     : indices of the simple roots inside `roots`
  R          : list of reflections, each represented by a canonical root (index into roots)
  gens       : the permutations of R induced by the simple reflections (r -> s r s)
  coxeter    : Coxeter matrix computed from the Gram matrix of the simple roots
"""
from fractions import Fraction as Fr
import itertools

# ---------------- arithmetic in Q(phi) -----------------
def num(a, b=0):
    return (Fr(a), Fr(b))
ZERO = num(0)
def add(x, y): return (x[0] + y[0], x[1] + y[1])
def sub(x, y): return (x[0] - y[0], x[1] - y[1])
def neg(x): return (-x[0], -x[1])
def mul(x, y):  # phi^2 = phi + 1
    a, b = x; c, d = y
    return (a * c + b * d, a * d + b * c + b * d)
def inv(x):
    # (a + b phi)^{-1}: norm N = a^2 + ab - b^2, conjugate a + b(1-phi) = (a+b) - b phi
    a, b = x; N = a * a + a * b - b * b
    assert N != 0
    return ((a + b) / N, -b / N)
def div(x, y): return mul(x, inv(y))
def sign(x):
    """exact sign of a + b*phi = (a + b/2) + (b/2) sqrt5"""
    a, b = x; u = a + b / 2; t = b / 2
    if t == 0: return (u > 0) - (u < 0)
    if u == 0: return (t > 0) - (t < 0)
    if (u > 0) == (t > 0): return 1 if u > 0 else -1
    # opposite signs: compare u^2 with 5 t^2
    if u * u > 5 * t * t: return 1 if u > 0 else -1
    return 1 if t > 0 else -1
def galois(x):  # phi -> 1 - phi
    a, b = x; return (a + b, -b)
def tofloat(x): return float(x[0]) + float(x[1]) * (1 + 5 ** .5) / 2

PHI = num(0, 1)
PHIINV = num(-1, 1)       # 1/phi = phi - 1

def vec(*xs): return tuple(x if isinstance(x, tuple) else num(x) for x in xs)
def dot(u, v):
    s = ZERO
    for x, y in zip(u, v): s = add(s, mul(x, y))
    return s
def vsub(u, v): return tuple(sub(x, y) for x, y in zip(u, v))
def vscale(c, u): return tuple(mul(c, x) for x in u)
def vneg(u): return tuple(neg(x) for x in u)
def reflect(a, v):
    """s_a(v) = v - 2 (a,v)/(a,a) a"""
    c = div(mul(num(2), dot(a, v)), dot(a, a))
    return vsub(v, vscale(c, a))
def canon(v):
    """canonical representative of the line through v up to sign: first nonzero coordinate positive"""
    for x in v:
        s = sign(x)
        if s != 0:
            return v if s > 0 else vneg(v)
    raise ValueError

# ---------------- simple roots -----------------
H = Fr(1, 2)
def simple_roots(name):
    if name in ('E6', 'E7', 'E8'):
        # Bourbaki: a1 = 1/2(1,-1,-1,-1,-1,-1,-1,1), a2 = e1+e2, a_{k} = e_{k-2}-e_{k-3} (k>=3)
        s = [vec(H, -H, -H, -H, -H, -H, -H, H), vec(1, 1, 0, 0, 0, 0, 0, 0)]
        for i in range(6):
            v = [0] * 8; v[i] = -1; v[i + 1] = 1; s.append(vec(*v))
        return s[:int(name[1])]
    if name == 'F4':
        return [vec(0, 1, -1, 0), vec(0, 0, 1, -1), vec(0, 0, 0, 1), vec(H, -H, -H, -H)]
    if name[0] == 'D':                      # D_n: e_i - e_{i+1}, e_{n-1} + e_n
        n = int(name[1:]); s = []
        for i in range(n - 1):
            v = [0] * n; v[i] = 1; v[i + 1] = -1; s.append(vec(*v))
        v = [0] * n; v[n - 2] = 1; v[n - 1] = 1; s.append(vec(*v)); return s
    if name[0] == 'A':                      # A_n in R^{n+1}: e_i - e_{i+1}
        n = int(name[1:]); s = []
        for i in range(n):
            v = [0] * (n + 1); v[i] = 1; v[i + 1] = -1; s.append(vec(*v))
        return s
    if name[0] == 'B':                      # B_n: e_i - e_{i+1}, e_n
        n = int(name[1:]); s = []
        for i in range(n - 1):
            v = [0] * n; v[i] = 1; v[i + 1] = -1; s.append(vec(*v))
        v = [0] * n; v[n - 1] = 1; s.append(vec(*v)); return s
    if name in ('H3', 'H4'):
        return find_simple_H(name)
    raise ValueError(name)

def full_H_roots(name):
    """All roots (norm^2 = 4) of H3 (icosahedron, 30 roots) and H4 (600-cell, 120 roots)."""
    out = set()
    if name == 'H3':
        base = [(PHI, num(1), PHIINV)]
        for i in range(3):
            for s in (1, -1):
                v = [ZERO] * 3; v[i] = num(2 * s); out.add(tuple(v))
        perms = [(0, 1, 2), (1, 2, 0), (2, 0, 1)]   # even permutations
        n = 3
    else:
        for i in range(4):
            for s in (1, -1):
                v = [ZERO] * 4; v[i] = num(2 * s); out.add(tuple(v))
        for signs in itertools.product((1, -1), repeat=4):
            out.add(tuple(num(s) for s in signs))
        base = [(PHI, num(1), PHIINV, ZERO)]
        perms = [p for p in itertools.permutations(range(4)) if parity(p) == 0]
        n = 4
    for b in base:
        for p in perms:
            for signs in itertools.product((1, -1), repeat=n):
                v = [None] * n
                for i in range(n):
                    v[p[i]] = mul(num(signs[i]), b[i])
                out.add(tuple(v))
    return sorted(out)

def parity(p):
    p = list(p); s = 0
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]: s ^= 1
    return s

def coxeter_gram_target(name):
    # target (a_i,a_j) for norm^2 4: m=2 -> 0, m=3 -> -2, m=5 -> -2 phi  (= -4 cos(pi/m))
    if name == 'H3': M = [[1, 3, 2], [3, 1, 5], [2, 5, 1]]
    else: M = [[1, 3, 2, 2], [3, 1, 3, 2], [2, 3, 1, 5], [2, 2, 5, 1]]
    val = {2: ZERO, 3: num(-2), 5: mul(num(-2), PHI)}
    return M, val

def find_simple_H(name):
    roots = full_H_roots(name)
    M, val = coxeter_gram_target(name)
    n = len(M)
    def bt(cur):
        if len(cur) == n: return cur
        for r in roots:
            if all(dot(r, c) == val[M[len(cur)][j]] for j, c in enumerate(cur)):
                res = bt(cur + [r])
                if res: return res
        return None
    return bt([])

# ---------------- root system, reflections, permutation action -----------------
class RootSystem:
    def __init__(self, name):
        self.name = name
        S = simple_roots(name)
        self.n = len(S)
        roots = list(S); idx = {r: i for i, r in enumerate(roots)}
        i = 0
        while i < len(roots):
            for a in S:
                r = reflect(a, roots[i])
                if r not in idx: idx[r] = len(roots); roots.append(r)
            i += 1
        self.roots = roots; self.ridx = idx
        self.simple = list(range(self.n))
        # reflections = lines
        lines = {}; R = []
        for r in roots:
            c = canon(r)
            if c not in lines: lines[c] = len(R); R.append(c)
        self.R = R; self.lidx = lines; self.N = len(R)
        self.gens = [self.perm_of(a) for a in S]
        self.sidx = [lines[canon(a)] for a in S]
        # Coxeter matrix from Gram matrix: cos^2(pi/m) = (a,b)^2/((a,a)(b,b))
        cos2 = {2: 0.0, 3: 0.25, 4: 0.5, 5: ((1 + 5 ** .5) / 4) ** 2, 6: 0.75}
        Mx = [[1] * self.n for _ in range(self.n)]
        for i in range(self.n):
            for j in range(self.n):
                if i != j:
                    a, b = S[i], S[j]
                    q = tofloat(dot(a, b)) ** 2 / (tofloat(dot(a, a)) * tofloat(dot(b, b)))
                    m = min(cos2, key=lambda k: abs(cos2[k] - q))
                    assert abs(cos2[m] - q) < 1e-9
                    assert sign(dot(a, b)) <= 0
                    Mx[i][j] = m
        self.coxeter = Mx
        self.S = S
    def perm_of(self, a):
        """permutation of R induced by conjugation with the reflection s_a: line r -> line s_a(r)"""
        return tuple(self.lidx[canon(reflect(a, r))] for r in self.R)
    def perm_of_map(self, T):
        """permutation of R induced by a map T on vectors sending lines of roots to lines of roots"""
        out = []
        for r in self.R:
            v = canon(T(r))
            for c in (num(1), num(Fr(1, 2)), num(2)):      # lines: allow rescaling (F4 similarity)
                w = vscale(c, v)
                if w in self.lidx: out.append(self.lidx[w]); break
            else:
                raise KeyError('T does not map roots to lines of roots')
        return tuple(out)

if __name__ == '__main__':
    for nm in ['H3', 'H4', 'F4', 'E6', 'E7', 'E8', 'D5']:
        rs = RootSystem(nm)
        print(nm, 'roots', len(rs.roots), 'reflections', rs.N, 'coxeter', rs.coxeter)
