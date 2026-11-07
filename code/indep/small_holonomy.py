#!/usr/bin/env python3
"""Independent check (written from scratch, imports nothing from the package).

For a type in {H3, F4}:
  * builds the root system exactly (coefficients in Z[phi] in the simple-root basis),
  * builds G = rho(W) as permutations of the reflections (= positive roots),
  * computes |Aut(G)| by counting generating tuples of involutions satisfying the Coxeter relations
    (no assumption that automorphisms preserve reflections),
  * computes the orbitals, rational eigenspaces of a generic commutant element, checks good constituents
    by BOTH the commutant criterion and character inner products (exact rationals),
  * builds pi for the outer class from an explicit outer automorphism found in the tuple search,
  * checks the witness conditions of the stable/swap criterion exactly.
"""
import sys, random, itertools
from fractions import Fraction
import sympy as sp

# ---- Z[phi] arithmetic: (a,b) = a + b*phi, phi^2 = phi + 1 ----
def zadd(x, y): return (x[0]+y[0], x[1]+y[1])
def zsub(x, y): return (x[0]-y[0], x[1]-y[1])
def zmul(x, y): return (x[0]*y[0]+x[1]*y[1], x[0]*y[1]+x[1]*y[0]+x[1]*y[1])
def zsign(x):
    # sign of a + b*phi = (2a+b + b sqrt5)/2
    p, q = 2*x[0]+x[1], x[1]
    if p >= 0 and q >= 0: return 0 if (p == 0 and q == 0) else 1
    if p <= 0 and q <= 0: return -1
    # opposite signs: compare p^2 with 5 q^2
    if p > 0: return 1 if p*p > 5*q*q else -1
    return 1 if 5*q*q > p*p else -1
Z0, Z1 = (0, 0), (1, 0)
PHI = (0, 1)

def cartan(typ):
    if typ == 'H3':
        n = 3; C = [[Z0]*n for _ in range(n)]
        for i in range(n): C[i][i] = (2, 0)
        C[0][1] = C[1][0] = (0, -1)   # -phi, m=5
        C[1][2] = C[2][1] = (-1, 0)   # m=3
        M = [[1,5,2],[5,1,3],[2,3,1]]
        return n, C, M
    if typ == 'F4':
        n = 4; C = [[Z0]*n for _ in range(n)]
        for i in range(n): C[i][i] = (2, 0)
        # alpha0, alpha1 long; alpha2, alpha3 short. C[i][j] = <alpha_j, alpha_i^vee>
        C[0][1] = C[1][0] = (-1, 0)
        C[1][2] = (-1, 0); C[2][1] = (-2, 0)
        C[2][3] = C[3][2] = (-1, 0)
        M = [[1,3,2,2],[3,1,4,2],[2,4,1,3],[2,2,3,1]]
        return n, C, M
    raise ValueError(typ)

def refl(i, v, C):
    n = len(v)
    c = Z0
    for j in range(n): c = zadd(c, zmul(v[j], C[i][j]))
    w = list(v); w[i] = zsub(w[i], c)
    return tuple(w)

def roots(typ):
    n, C, M = cartan(typ)
    simple = [tuple(Z1 if j == i else Z0 for j in range(n)) for i in range(n)]
    R = set(simple); frontier = list(simple)
    while frontier:
        nf = []
        for v in frontier:
            for i in range(n):
                w = refl(i, v, C)
                if w not in R: R.add(w); nf.append(w)
        frontier = nf
    pos = sorted(v for v in R if all(zsign(c) >= 0 for c in v))
    assert all(tuple((-c[0], -c[1]) for c in v) in R for v in pos)
    assert 2*len(pos) == len(R)
    return n, C, M, pos

def neg(v): return tuple((-c[0], -c[1]) for c in v)

def mul(p, q): return tuple(p[i] for i in q)   # (p*q)(i) = p(q(i))
def inv(p):
    r = [0]*len(p)
    for i, x in enumerate(p): r[x] = i
    return tuple(r)
def order(p):
    e = tuple(range(len(p))); k = 1; q = p
    while q != e: q = mul(p, q); k += 1
    return k

def closure(gens):
    e = tuple(range(len(gens[0])))
    G = {e}; fr = [e]
    while fr:
        nf = []
        for g in fr:
            for s in gens:
                h = mul(s, g)
                if h not in G: G.add(h); nf.append(h)
        fr = nf
    return G

def main(typ):
    n, C, M, pos = roots(typ)
    N = len(pos); idx = {v: i for i, v in enumerate(pos)}
    def line(v):
        return idx[v] if v in idx else idx[neg(v)]
    gens = [tuple(line(refl(i, v, C)) for v in pos) for i in range(n)]
    G = closure(gens); Gl = sorted(G)
    print(f"{typ}: |R| = {N}, |rho(W)| = {len(G)}")
    e = tuple(range(N))
    # the reflection s_beta as an element of rho(W): find by conjugating a simple generator
    # build words: element -> rho(s_beta)
    refl_elt = {}
    for i in range(n): refl_elt[line(tuple(Z1 if j == i else Z0 for j in range(n)))] = gens[i]
    changed = True
    while changed:
        changed = False
        for r, t in list(refl_elt.items()):
            for i in range(n):
                r2 = gens[i][r]
                if r2 not in refl_elt:
                    refl_elt[r2] = mul(mul(gens[i], t), gens[i]); changed = True
    assert len(refl_elt) == N and len(set(refl_elt.values())) == N, "rho injective on R"
    # check refl_elt consistent: conjugation action of rho(s_beta) on R is the permutation itself? (rho(r) acts on R by r'->r r' r)
    # centre
    cent = [g for g in Gl if all(mul(g, s) == mul(s, g) for s in gens)]
    print("  centre of rho(W) has order", len(cent))
    # involutions and their classes
    invols = [g for g in Gl if g != e and mul(g, g) == e]
    def conj_class(x):
        cl = {x}; fr = [x]
        while fr:
            nf = []
            for y in fr:
                for s in gens:
                    z = mul(mul(s, y), s)  # s is an involution
                    if z not in cl: cl.add(z); nf.append(z)
            fr = nf
        return frozenset(cl)
    classes = []; seen = set()
    for g in invols:
        if g not in seen:
            cl = conj_class(g); classes.append(cl); seen |= cl
    print("  involution class sizes:", sorted(len(c) for c in classes))
    reflset = set(refl_elt.values())
    print("  reflection classes:", sorted(len(c) for c in classes if c <= reflset))
    # ---- count Aut(G): generating tuples of involutions (t_i) with ord(t_i t_j) | m_ij,
    # t_i in a class of the same size as rho(s_i). Each gives hom W->G; surjective => kernel order |Z(W)|<=2, central, = Z(W).
    size_of = {}
    for c in classes:
        for g in c: size_of[g] = len(c)
    cand = [[g for g in invols if size_of[g] == size_of[gens[i]]] for i in range(n)]
    ordcache = {}
    def okpair(a, b, m):
        p = mul(a, b)
        # order divides m
        q = e
        for _ in range(m): q = mul(p, q)
        return q == e
    autos = []
    # fix t_0 among representatives up to conjugacy: count all, but to save time enumerate t_0 in full (groups small)
    def rec(t):
        k = len(t)
        if k == n:
            autos.append(tuple(t)); return
        for c in cand[k]:
            if all(okpair(t[j], c, M[j][k]) for j in range(k)):
                rec(t + [c])
    rec([])
    gen_autos = [t for t in autos if len(closure(list(t))) == len(G)]
    print(f"  tuples satisfying relations: {len(autos)}, generating: {len(gen_autos)}  => |Aut(G)| = {len(gen_autos)}, |Out(G)| = {Fraction(len(gen_autos), len(G)//len(cent))}")
    # identify an outer one: inner ones are conjugates of gens
    inner = set(tuple(mul(mul(g, s), inv(g)) for s in gens) for g in Gl)
    outer = [t for t in gen_autos if t not in inner]
    print("  inner tuples:", len(inner), " outer tuples:", len(outer))
    # permutation matrices
    def pmat(p):
        m = sp.zeros(N, N)
        for i in range(N): m[p[i], i] = 1
        return m
    # ---- orbitals and commutant
    pairs = {}
    orbit_id = {}
    k = 0
    for a in range(N):
        for b in range(N):
            if (a, b) in orbit_id: continue
            fr = [(a, b)]; orbit_id[(a, b)] = k
            while fr:
                nf = []
                for (x, y) in fr:
                    for s in gens:
                        z = (s[x], s[y])
                        if z not in orbit_id: orbit_id[z] = k; nf.append(z)
                fr = nf
            k += 1
    norb = k
    O = [sp.zeros(N, N) for _ in range(norb)]
    for (a, b), w in orbit_id.items(): O[w][a, b] = 1
    print("  number of orbitals (rank of commutant):", norb)
    random.seed(1)
    X = sp.zeros(N, N)
    for w in range(norb):
        c = random.randint(1, 50); X += c*(O[w] + O[w].T)
    x = sp.Symbol('x')
    fac = sp.factor_list(X.charpoly(x).as_expr())
    good = []
    for f, mult in fac[1]:
        if sp.degree(f, x) == 1:
            lam = sp.solve(f, x)[0]
            B = (X - lam*sp.eye(N)).nullspace()
            B = sp.Matrix.hstack(*B)
            d = B.shape[1]
            # commutant criterion: each O_w maps U to U as a scalar
            Pinv = (B.T*B).inv()
            scal = True
            for w in range(norb):
                Y = O[w]*B
                coeff = Pinv*(B.T*Y)
                if B*coeff != Y: scal = False; break
                if coeff != coeff[0, 0]*sp.eye(d): scal = False; break
            # character criterion
            P = B*Pinv*B.T
            chiU = {g: sum(P[i, g[i]] for i in range(N)) for g in Gl}  # tr(P rho(g)) : rho(g) e_i = e_{g(i)} -> entry (g(i), i); tr(P*rho(g)) = sum_i P[i, g(i)]
            perm = {g: sum(1 for i in range(N) if g[i] == i) for g in Gl}
            nn = sum(chiU[g]**2 for g in Gl)/len(Gl)
            ip = sum(chiU[g]*perm[g] for g in Gl)/len(Gl)
            movers = [i for i in range(n) if pmat(gens[i])*B != B]
            print(f"  eigenvalue {lam}: dim {d}, commutant-scalar {scal}, <chi,chi>={nn}, <chi,perm>={ip}, moved by simple refl {movers}")
            if scal and nn == 1 and ip == 1:
                good.append(B)
    # permutation character decomposition sanity: norm of perm char
    perm = {g: sum(1 for i in range(N) if g[i] == i) for g in Gl}
    print("  <perm,perm> =", Fraction(sum(perm[g]**2 for g in Gl), len(Gl)), "(= number of orbitals)")
    # ---- outer pi from an outer tuple
    if outer:
        t = outer[0]
        # theta: gens[i] -> t[i]; extend to G by BFS words
        theta = {e: e}; fr = [e]
        while fr:
            nf = []
            for g in fr:
                for i in range(n):
                    h = mul(gens[i], g)
                    if h not in theta: theta[h] = mul(t[i], theta[g]); nf.append(h)
            fr = nf
        assert all(theta[mul(a, b)] == mul(theta[a], theta[b]) for a in Gl[:50] for b in Gl)
        # does theta preserve reflections?
        refl_of = {v: r for r, v in refl_elt.items()}
        pres = all(theta[refl_elt[r]] in refl_of for r in range(N))
        print("  outer theta preserves reflections:", pres)
        pi = tuple(refl_of[theta[refl_elt[r]]] for r in range(N))
        ok = all(mul(mul(pi, g), inv(pi)) == theta[g] for g in Gl)
        print("  pi rho(w) pi^-1 = theta(rho(w)) for all w:", ok)
        Pi = pmat(pi)
        for j, B in enumerate(good):
            # image of U under pi
            imgs = []
            PB = Pi*B
            for k2, B2 in enumerate(good):
                M2 = sp.Matrix.hstack(B2, PB)
                if M2.rank() == B2.shape[1] and B2.shape[1] == B.shape[1]: imgs.append(k2)
            print(f"  pi maps good constituent {j} (dim {B.shape[1]}) onto constituent(s) {imgs}")
        # witnesses
        for j, B in enumerate(good):
            d = B.shape[1]
            for eps in (1, -1):
                found = None
                for hcount, h in enumerate([e] + [g for g in Gl if g != e]):
                    T = pmat(mul(h, pi))
                    for powr, Q in ((1, T), (2, T*T)):
                        # dim of {v in U : Q v = eps v}: solve (Q - eps) B c = 0
                        K = ((Q - eps*sp.eye(N))*B).nullspace()
                        if K:
                            found = (hcount, powr, len(K)); break
                    if found: break
                print(f"  constituent {j}, eps={eps}: first witness (h index, power of h*pi, dim) = {found}")
        # Specifically for case (i) vs (ii): check whether some h*pi has eigenvalue -1 on U directly
    return

if __name__ == '__main__':
    for typ in sys.argv[1:]:
        main(typ)
