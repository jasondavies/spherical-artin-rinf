#!/usr/bin/env python3
"""Exact finite cross-checks for the uniform proofs of Theorem B.

The all-rank arguments are in the paper. These checks do not replace them.
No scratch modules, floating point, or Reidemeister averaging formula are used.
Run from any directory; requires SymPy. Default: dihedral m = 3,...,22.
"""

import argparse
from itertools import combinations
from math import comb

import sympy as sp
from sympy.polys.matrices import DomainMatrix


def canonical(v):
    sign = next(x for x in v if x)
    return tuple(v) if sign > 0 else tuple(-x for x in v)


def classical_characters():
    # Count fixed root lines directly, independently of the polynomial formulas.
    for n in range(3, 13):
        roots_d = []
        for i, j in combinations(range(n), 2):
            for sign in (-1, 1):
                v = [0] * n
                v[i], v[j] = 1, sign
                roots_d.append(tuple(v))
        roots_b = roots_d + [tuple(int(i == j) for i in range(n)) for j in range(n)]

        def fixed(roots, p, signs):
            count = 0
            for v in roots:
                w = [0] * n
                for j in range(n):
                    w[p[j]] = signs[j] * v[j]
                count += canonical(w) == v
            return count

        for c in range(n // 2 + 1):
            for a in range(n - 2 * c + 1):
                b = n - 2 * c - a
                p = list(range(n))
                signs = [1] * a + [-1] * b + [1] * (2 * c)
                for j in range(a + b, n, 2):
                    p[j], p[j + 1] = j + 1, j
                chi_d = a * (a - 1) + b * (b - 1) + 2 * c
                assert fixed(roots_d, p, signs) == chi_d
                assert fixed(roots_b, p, signs) == chi_d + a + b
        if n % 2 == 0:
            p = [j ^ 1 for j in range(n)]
            signs = [1 if j % 2 == 0 else -1 for j in range(n)]
            assert fixed(roots_b, p, signs) == fixed(roots_d, p, signs) == 0
    print("Classical character formulas: direct root-line checks through rank 12 passed")

    for family, minimum in [("B", 3), ("D", 5)]:
        for n in range(minimum, 121):
            for c in range(n // 2 + 1):
                for a in range(n - 2 * c + 1):
                    b = n - 2 * c - a
                    if family == "D" and b % 2:
                        continue
                    chi = a * (a - 1) + b * (b - 1) + 2 * c
                    if family == "B":
                        chi += a + b
                        if chi == (n - 2)**2 + 2:
                            assert (c == 1 and a * b == 0) or (n, a, b, c) == (6, 3, 3, 0)
                        if chi == n * n - 2 * n + 2:
                            assert c == 0 and min(a, b) == 1
                    elif chi == (n - 2) * (n - 3) + 2:
                        assert (c == 1 and a * b == 0) or (c == 0 and min(a, b) == 2)
            if family == "D":
                assert comb(n, 2) != n * (n - 1)
    assert comb(6, 3) // 2 == 10 != 30
    print("Character coincidences and exceptional class-size exclusions through rank 120 passed")

    # Independently compute conjugacy orbits, rather than reuse the class-size formulas.
    # A signed permutation lists the images of e_1,...,e_n as signed indices.
    def multiply(p, q):
        return tuple((1 if j > 0 else -1) * p[abs(j) - 1] for j in q)

    def class_size(n, family, representative, central_quotient):
        identity = tuple(range(1, n + 1))
        generators = []
        for j in range(n - 1):
            g = list(identity)
            g[j], g[j + 1] = g[j + 1], g[j]
            generators.append(tuple(g))
        generators.append(tuple(-i if i <= (1 if family == "B" else 2) else i
                                for i in identity))

        def quotient(p):
            return min(p, tuple(-i for i in p)) if central_quotient else p

        seen = {quotient(representative)}
        pending = list(seen)
        while pending:
            p = pending.pop()
            for g in generators:  # Each chosen generator is an involution.
                conjugate = quotient(multiply(multiply(g, p), g))
                if conjugate not in seen:
                    seen.add(conjugate)
                    pending.append(conjugate)
        return len(seen)

    for n in range(5, 13):
        reflection = (2, 1, *range(3, n + 1))
        diagonal = (-1, -2, *range(3, n + 1))
        for central_quotient in (False, n % 2 == 0):
            assert class_size(n, "D", reflection, central_quotient) == n * (n - 1)
            assert class_size(n, "D", diagonal, central_quotient) == comb(n, 2)
    assert class_size(6, "B", (-1, -2, -3, 4, 5, 6), False) == 20
    assert class_size(6, "B", (-1, -2, -3, 4, 5, 6), True) == 10
    assert class_size(6, "B", (2, 1, 3, 4, 5, 6), True) == 30
    print("Direct conjugacy orbits: B6 and D5-D12 class-size exclusions passed")


def determinant(matrix):
    return int(DomainMatrix.from_Matrix(matrix).det())


def dihedral(m):
    I = sp.eye(m)
    C, S = sp.zeros(m), sp.zeros(m)
    for j in range(m):
        C[(j + 1) % m, j] = 1
        S[-j % m, j] = 1
    R = C**2
    q = m if m % 2 else m // 2
    group = [(R**k) * (S if reflection else I) for reflection in (False, True) for k in range(q)]
    assert len({tuple(g) for g in group}) == 2 * q

    if m % 2 and m % 3 == 0:
        U = sp.Matrix(m, 2, lambda j, k: int(j % 3 == k) - int(j % 3 == 2))
        left = (U.T * U).inv() * U.T
        chi = []
        for g in group:
            action = left * g * U
            assert U * action == g * U
            chi.append(sp.trace(action))
        assert sum(x * x for x in chi) == len(group)
        assert sum(x * sp.trace(g) for x, g in zip(chi, group)) == len(group)
        assert [d for d in sp.divisors(m) if sp.totient(d) == 2] == [3]
        print(f"I2({m}): unique rational degree-2 constituent, irreducibility and multiplicity verified")
        return

    if m % 4 == 0:
        U = sp.Matrix(m, 2, lambda j, k: (-1)**(j // 2) if j % 2 == k else 0)
        assert R * U == -U and S * U == U * sp.diag(1, -1)
        multiplicities = {}
        for cr in (1, -1):
            for cs in (1, -1):
                total = sum(cr**k * cs**r * sp.trace(R**k * S**r) for r in (0, 1) for k in range(q))
                multiplicities[cr, cs] = total / len(group)
        assert multiplicities == {(1, 1): 2, (1, -1): 0, (-1, 1): 1, (-1, -1): 1}
        print(f"I2({m}): the two nontrivial rational lines and stable/swap characters verified")
        return

    if m % 2:
        D, d = I - C - C.T, I[:, 0] + I[:, 1]
        assert determinant(D) == -1
        assert (I + C) * (I - C + C**2) == I + C**3
        assert determinant(I + C) == determinant(I + C**3) == 2
        assert (D - I) * I[:, 0] + (I - S) * d == -2 * I[:, m - 1]
        assert (D - I) * I[:, 1] + (I - R * S) * d == -2 * I[:, 2]
    else:
        D, d = sp.zeros(m), sp.zeros(m, 1)
        for j in range(0, m, 2):
            k = (j + q) % m
            D[j, j], D[j, k], D[k, j], D[k, k] = 1, 2, 2, 5
        assert determinant(D) == 1
        assert D**2 - 6 * D + I == sp.zeros(m)
    assert D * R == R * D and D * S == S * D

    def in_lattice(vector):
        if any(x.q != 1 for x in vector):
            return False
        parity = {int(x) % 2 for x in vector}
        return parity == {0} or (m % 2 == 0 and parity == {1})

    lattice_generators = [2 * I[:, j] for j in range(m)]
    if m % 2 == 0:
        lattice_generators.append(sp.ones(m, 1))
    for linear, translation in [(D, d), (D.inv(), -D.inv() * d)]:
        assert all(in_lattice(linear * v) for v in lattice_generators)
        for j, g in [(0, S), (1, R * S)]:
            assert in_lattice((linear - I) * I[:, j] + (I - g) * translation)
    dets = [determinant(I - g * D) for g in group]
    assert all(dets)
    print(f"I2({m}): affine map and inverse preserve lattice/extension; all {len(group)} determinants nonzero")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-m", type=int, default=22)
    args = parser.parse_args()
    classical_characters()
    for m in range(3, args.max_m + 1):
        dihedral(m)
    print("ALL CHECKS PASSED (finite cross-checks; uniform proofs are in the manuscript)")
