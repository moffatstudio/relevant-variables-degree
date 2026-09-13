"""Referee check: two octahedra glued at one vertex (11 variables, 16 face-triples), f = (1/4) sum eps_S chi_S.
Verify that for every sign vector eps in {+-1}^16, f is NOT {+-1}-valued.
Also check the two other 'disjoint-sum' structures the proof kills:
  (A) delta=4, |N|=4:  4 unit quadratics on a 4-cycle i-a-j-b + cubics {c,i,a},{c,a,j},{c,j,b},{c,b,i} + an octahedron on 6 more vars.
  (B) delta=4, {2,2} with the missing link shape L4: linear {i},{j}, cubics {i or j} x pairs of {a,b,c}, + octahedron on 6 more vars.
For (A),(B) the sign space is 2^16 as well.
"""
import itertools
import numpy as np

n = 11


def octahedron(verts):
    """8 faces of the octahedron on 6 vertices verts, antipodal pairs (0,1),(2,3),(4,5)."""
    a, b, c, d, e, f = verts
    faces = []
    for p in (a, b):
        for q in (c, d):
            for r in (e, f):
                faces.append((p, q, r))
    return faces


X = np.array(list(itertools.product([-1, 1], repeat=n)), dtype=np.int8)  # 2048 x 11


def char_matrix(terms):
    M = np.ones((X.shape[0], len(terms)), dtype=np.int8)
    for j, S in enumerate(terms):
        for v in S:
            M[:, j] *= X[:, v]
    return M  # 2048 x 16


def never_boolean(terms, name):
    M = char_matrix(terms).astype(np.int16)  # values +-1
    k = len(terms)
    assert k == 16
    signs = np.array(list(itertools.product([-1, 1], repeat=k)), dtype=np.int16)  # 65536 x 16
    bad = 0
    for start in range(0, signs.shape[0], 4096):
        S = signs[start:start + 4096]
        vals = S @ M.T  # chunk x 2048, equals 4 f(x)
        boolean_rows = np.all(np.abs(vals) == 4, axis=1)
        bad += int(boolean_rows.sum())
    print(f"{name}: sign vectors giving a Boolean f: {bad} (of {signs.shape[0]})")


# glued octahedra: vertex 0 shared; octahedron 1 on {0,1,2,3,4,5}, octahedron 2 on {0,6,7,8,9,10}
T1 = octahedron([0, 1, 2, 3, 4, 5]) + octahedron([0, 6, 7, 8, 9, 10])
assert len(set(T1)) == 16
never_boolean(T1, "glued octahedra (C4+C4 sub-case)")

# (A) i=0,a=1,j=2,b=3,c=4 ; octahedron on 5..10
TA = [(0, 1), (1, 2), (2, 3), (3, 0), (4, 0, 1), (4, 1, 2), (4, 2, 3), (4, 3, 0)] + octahedron([5, 6, 7, 8, 9, 10])
never_boolean(TA, "delta=4 |N|=4 structure")

# (B) i=0,j=1,a=2,b=3,c=4 ; octahedron on 5..10
TB = [(0,), (1,), (0, 2, 3), (0, 3, 4), (0, 2, 4), (1, 2, 3), (1, 3, 4), (1, 2, 4)] + octahedron([5, 6, 7, 8, 9, 10])
never_boolean(TB, "delta=4 {2,2} with L4 links (patch structure)")

# sanity: the CHS-type 10-variable function should exist; check a single octahedron (6 vars, 8 terms) is never Boolean alone
