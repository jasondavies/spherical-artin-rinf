#!/usr/bin/env python3
"""Exact verification of Proposition C, including torsion-sensitive R = 18.

Uses only SymPy and the standard library. No root approximations, numerical
determinants, or torsion-free averaging formula enter the computation.
The affine generators are the images of the two Artin generators under f.
"""

from collections import Counter, deque

import sympy as sp


I = sp.eye(5)
E = [I[:, j] for j in range(5)]
C = sp.zeros(5)
S = sp.zeros(5)
for j in range(5):
    C[(j + 1) % 5, j] = 1
    S[-j % 5, j] = 1
D = I - C - C.T
d = E[0] + E[1]
generators = [(E[0], S), (E[1], C**2 * S)]


def key(matrix):
    return tuple(matrix)


def mul(left, right):
    a, g = left
    b, h = right
    return a + g * b, g * h


def product(factors):
    result = (sp.zeros(5, 1), I)
    for factor in factors:
        result = mul(result, factor)
    return result


def integral(vector):
    return all(x.q == 1 for x in vector)


def main():
    assert product([generators[j % 2] for j in range(5)]) == product(
        [generators[1 - j % 2] for j in range(5)]
    )
    assert D.det() == -1
    assert D.inv() == I - C**2 - C**3
    assert D * C == C * D and D * S == S * D
    assert D.charpoly().as_expr().factor() == (
        (sp.Symbol("lambda") + 1) * (sp.Symbol("lambda")**2 - 3 * sp.Symbol("lambda") + 1)**2
    )

    # The extension is encoded by its ten parity cosets, not by a split
    # semidirect product with the translation lattice 2 Z^5.
    sections = {key(I): (sp.zeros(5, 1), I)}
    queue = deque(sections)
    while queue:
        a, g = sections[queue.popleft()]
        for generator in generators:
            v, h = mul((a, g), generator)
            hk = key(h)
            parity = v.applyfunc(lambda x: x % 2)
            if hk not in sections:
                sections[hk] = parity, h
                queue.append(hk)
            else:
                assert sections[hk][0] == parity
    assert len(sections) == 10
    # Squares and their conjugates supply every 2 e_j translation.
    assert mul(generators[0], generators[0]) == (2 * E[0], I)
    assert {key(g * E[0]) for _, g in sections.values()} == {key(e) for e in E}

    for correction, (a, g) in zip([-2 * E[4], -2 * E[2]], generators):
        assert (D - I) * a + (I - g) * d == correction
    for a, g in sections.values():
        assert integral(((D - I) * a + (I - g) * d) / 2)
        dinv = -D.inv() * d
        assert integral(((D.inv() - I) * a + (I - g) * dinv) / 2)
    print("Artin relation, actual extension, lattice and affine automorphism: verified")

    rotations = [(I - C**k * D).det() for k in range(5)]
    reflections = [(I - C**k * S * D).det() for k in range(5)]
    assert rotations == [2, 22, 22, 22, 22]
    assert reflections == [-10] * 5
    print(f"det(I - gD): rotations {rotations}; reflections {reflections}")

    torsion = (sp.Matrix([-1, 0, -1, 1, 1]), C)
    assert integral((torsion[0] - sections[key(C)][0]) / 2)
    assert product([torsion] * 5) == (sp.zeros(5, 1), I)
    assert C != I
    print("An element of order 5 in the actual quotient: verified")

    # First count: verify the four cyclic quotients and centralizer actions
    # displayed in the manuscript. An onto functional modulo |det M| that
    # annihilates M Z^5 identifies Z^5 / M Z^5 with that cyclic group.
    rows = [
        (I, [0, 0, 0, 0, 0], 2, [1, 1, 1, 1, 1], 0, [(C, 1, 0), (S, 1, 1)], 1),
        (C, [1, 0, 1, 1, 1], 22, [1, 5, 3, 15, 9], 0, [(C, 5, 6)], 6),
        (C**2, [0, 1, 1, 0, 0], 22, [1, 3, 9, 5, 15], 0, [(C, 3, 4)], 6),
        (S, [1, 0, 0, 0, 0], 10, [5, 1, 7, 3, 9], 1, [(S, 9, 1)], 5),
    ]
    sector_counts = []
    for g, a_list, modulus, ell_list, j, actions, expected in rows:
        a, ell = sp.Matrix(a_list), sp.Matrix([ell_list])
        assert sections[key(g)][0] == a
        matrix = I - g * D
        assert abs(matrix.det()) == modulus and ell[j] == 1
        assert all(x % modulus == 0 for x in ell * matrix)
        for h, slope, intercept in actions:
            assert h * g == g * h
            b = sections[key(h)][0]
            for k in range(modulus):
                v = a + 2 * k * E[j]
                x = (b + h * v - g * (D * b + (I - h) * d) - a) / 2
                assert integral(x)
                assert (ell * x)[0] % modulus == (slope * k + intercept) % modulus
        unseen = set(range(modulus))
        count = 0
        while unseen:
            todo = [unseen.pop()]
            count += 1
            for k in todo:
                for _, slope, intercept in actions:
                    kk = (slope * k + intercept) % modulus
                    if kk in unseen:
                        unseen.remove(kk)
                        todo.append(kk)
        assert count == expected
        sector_counts.append(count)
    assert sector_counts == [1, 6, 6, 5]
    print(f"Centralizer orbit counts over 1, C, C^2, S: {sector_counts}; R = 18")

    # Second count: independently enumerate all 140 translation-twisted
    # classes, then act by all ten holonomy lifts. Coset equality is checked
    # by exact inverse matrices, without the cyclic quotient table above.
    inverses, representatives = {}, {}
    for gk, (_, g) in sections.items():
        matrix = I - g * D
        inverse = matrix.inv()
        inverses[gk] = inverse

        def coset(x):
            return tuple(z % 1 for z in inverse * x)

        zero = sp.zeros(5, 1)
        reps = {coset(zero): zero}
        queue = deque(reps)
        while queue:
            x = reps[queue.popleft()]
            for e in E:
                y = x + e
                yk = coset(y)
                if yk not in reps:
                    reps[yk] = y
                    queue.append(yk)
        assert len(reps) == abs(matrix.det())
        representatives[gk] = reps
    nodes = {(gk, xk) for gk, reps in representatives.items() for xk in reps}
    assert len(nodes) == 140

    def act(hk, node, translation=d):
        gk, xk = node
        a, g = sections[gk]
        b, h = sections[hk]
        v = a + 2 * representatives[gk][xk]
        target = h * g * h.T
        tk = key(target)
        w = b + h * v - target * (D * b + (I - h) * translation)
        x = (w - sections[tk][0]) / 2
        assert integral(x)
        return tk, tuple(z % 1 for z in inverses[tk] * x)

    seen, sizes = set(), []
    for node in nodes:
        if node in seen:
            continue
        orbit = {act(hk, node) for hk in sections}
        assert orbit <= nodes and not orbit & seen
        seen.update(orbit)
        sizes.append(len(orbit))
    assert seen == nodes and Counter(sizes) == {10: 13, 2: 5}
    fixed = [sum(act(hk, node) == node for node in nodes) for hk in sections]
    assert sorted(fixed) == [0] * 5 + [10] * 4 + [140]
    assert sum(fixed) == 10 * 18
    # The scratch script chose the complementary translation vector.
    # It differs by a central translation and an inner translation in 2 Z^5.
    original_d = sp.ones(5, 1) - d
    original_fixed = [sum(act(hk, node, original_d) == node for node in nodes) for hk in sections]
    assert sum(original_fixed) == 10 * 18
    print("Full 140-class enumeration: 13 orbits of size 10 and 5 of size 2")
    print("Burnside check: (140 + 4*10 + 5*0)/10 = 18 (also for the scratch translation)")
    print("Determinant average = 14; it is not the Reidemeister number")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
