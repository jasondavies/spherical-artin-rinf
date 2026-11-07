"""Exact outer-case certificates, requiring complete constituents and both signs.

Numerical discovery supplies candidates; exact arithmetic verifies their dimensions,
scalar commutants, stable/swap images and nonzero sign-eigenvector spaces.
"""
from collections import Counter
import sys
import numpy as np
from sympy import Matrix
from eig import outer_check
from analyze import orbitals
from certify import nullspace_int

EXPECTED = {'H3': [4], 'H4': [16, 25], 'F4': [2, 2]}


def validate_coverage(name, good, witnesses):
    if sorted(B.shape[1] for B in good) != EXPECTED[name]:
        raise ValueError(f'{name}: missing or incorrect outer-case constituents')
    kind = 'swap' if name == 'F4' else 'stable'
    expected = Counter((kind, a, eps) for a in range(len(good)) for eps in (1, -1))
    if Counter((k, a, eps) for k, a, eps, _ in witnesses) != expected:
        raise ValueError(f'{name}: incomplete or duplicate sign witnesses')


def verify(name):
    C, G, good, res = outer_check(name)
    if res is None:
        raise ValueError(f'{name}: missing outer automorphism')
    validate_coverage(name, good, res['wit'])
    lab, k = orbitals(C)
    A = [(lab == i).astype(np.int64) for i in range(k)]
    rng = np.random.default_rng(7)
    X = sum(int(ci) * a for ci, a in zip(rng.integers(1, 50, size=k), A))
    X = X + X.T
    N = C.N
    identity = np.eye(N, dtype=np.int64)
    pi = np.asarray(res['pi'])
    if sorted(pi.tolist()) != list(range(N)):
        raise ValueError(f'{name}: invalid normalising permutation')
    pinv = np.argsort(pi)
    for generator in C.rp:
        G.index(pi[generator][pinv])  # Exact membership; an invalid image raises.
    if any(all(np.array_equal(h[g][np.argsort(h)], pi[g][pinv]) for g in C.rp) for h in G.E):
        raise ValueError(f'{name}: the proposed outer automorphism is inner')

    lambdas = [int(round((B.T @ X @ B)[0, 0])) for B in good]
    if len(set(lambdas)) != len(good):
        raise ValueError(f'{name}: candidate constituents are not distinct eigenspaces')
    bases = [nullspace_int(X - lam * identity).T for lam in lambdas]
    P = Matrix(identity[:, pi].tolist())
    for a, B in enumerate(bases):
        if B.cols != good[a].shape[1] or B.cols == 0:
            raise ValueError(f'{name}: wrong exact dimension for constituent {a}')
        row = next(i for i in range(N) if B[i, 0] != 0)
        for orbital in A:
            OB = Matrix(orbital.tolist()) * B
            if OB != B * (OB[row, 0] / B[row, 0]):
                raise ValueError(f'{name}: non-scalar commutant on constituent {a}')
        target = 1 - a if name == 'F4' else a
        if Matrix((X - lambdas[target] * identity).tolist()) * P * B != Matrix.zeros(N, B.cols):
            raise ValueError(f'{name}: incorrect stable/swap image for constituent {a}')

    for kind, a, eps, x in res['wit']:
        if not 0 <= x < len(G.E):
            raise ValueError(f'{name}: invalid witness group index')
        q = G.E[x][pi]
        if kind == 'swap':
            q = q[q]
        Q = Matrix(identity[:, q].tolist())
        dimension = bases[a].cols - ((Q - eps * Matrix.eye(N)) * bases[a]).rank()
        if dimension <= 0:
            raise ValueError(f'{name}: no exact eigenvector for constituent {a}, sign {eps}')
        print(f'EXACT {name}: {kind} constituent {a}, eps={eps}, eigenspace dimension={dimension}', flush=True)


if __name__ == '__main__':
    if not sys.argv[1:]:
        sys.exit('Usage: certify_outer.py H3|F4|H4 [...]')
    for name in sys.argv[1:]:
        if name not in EXPECTED:
            sys.exit(f'Unsupported outer case: {name}')
        verify(name)
    print('ALL CHECKS PASSED')
