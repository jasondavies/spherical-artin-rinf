"""Minimal permutation-group utilities (independent code).

A permutation of {0..N-1} is a uint8/uint16 numpy row p with p[r] = image of r.
Composition: (p o q)[r] = p[q[r]]  ==  p[q]  in numpy indexing.
"""
import numpy as np

def enumerate_group(gens, limit=5_000_000):
    """All elements of <gens> as rows of a numpy array (identity first), plus a dict bytes->index."""
    N = len(gens[0])
    dt = np.uint8 if N < 256 else np.uint16
    G = [np.asarray(g, dtype=dt) for g in gens]
    e = np.arange(N, dtype=dt)
    rows = [e]; index = {e.tobytes(): 0}
    frontier = e[None, :]
    while len(frontier):
        new = []
        for g in G:
            cand = frontier[:, g]           # x o g
            for row in cand:
                k = row.tobytes()
                if k not in index:
                    index[k] = len(rows); rows.append(row); new.append(row)
        frontier = np.array(new, dtype=dt) if new else np.zeros((0, N), dt)
        if len(rows) > limit: raise RuntimeError('group too large')
    return np.array(rows, dtype=dt), index

def inverse(p):
    q = np.empty_like(p); q[p] = np.arange(len(p), dtype=p.dtype); return q

def order(p):
    e = np.arange(len(p)); q = p.copy(); k = 1
    while not np.array_equal(q, e): q = p[q]; k += 1
    return k

def centre(E, gens):
    mask = np.ones(len(E), bool)
    for g in gens:
        g = np.asarray(g, dtype=E.dtype)
        mask &= np.all(E[:, g] == g[E], axis=1)      # x o g == g o x
    return np.where(mask)[0]

def generated_order(gens):
    from sympy.combinatorics import Permutation, PermutationGroup
    return PermutationGroup([Permutation([int(x) for x in g]) for g in gens]).order()
