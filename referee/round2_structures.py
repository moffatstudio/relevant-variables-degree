"""Round-2 referee check: the three term-structures that the proof excludes only via the disjoint-sum lemma
are never Boolean, for ANY choice of the 16 signs (2^16 sign vectors each).

  (1) glued octahedra (delta = 0, link(v) = C_4 + C_4, v_1, v_2 in different octahedra)
  (2) delta = 4, {2,2}: {i},{j}, iab, ibc, iac, jab, jbc, jac  + octahedron on the other 6 variables
  (3) delta = 4, {1,1,1,1}, |N| = 4: ia, aj, jb, bi, iac, ajc, jbc, bic  + octahedron on the other 6
  (4) delta = 0, C_4 + C_4 with v_1, v_2 in the SAME octahedron: octahedron on 5 variables with one
      vertex doubled is not a simplicial structure; the proof's case is "octahedron on {v,4 others} + octahedron on 6"
      which is impossible as a 5-vertex closed surface; we instead test the literal hypergraph: two octahedra
      sharing NO vertex would need 12 variables, so case (4) is vacuous. Not tested.

f = (1/4) sum_S eps_S chi_S is Boolean iff sum_S eps_S chi_S(x) in {+4,-4} for all x in {-1,1}^11.
"""
import itertools
import numpy as np

n = 11
pts = np.array(list(itertools.product([1, -1], repeat=n)), dtype=np.int8)  # 2048 x 11


def octahedron(vs):
    """vs: 6 vertices, antipodal pairs (vs[0],vs[1]),(vs[2],vs[3]),(vs[4],vs[5]). Faces = one from each pair."""
    return [tuple(sorted((a, b, c))) for a in vs[0:2] for b in vs[2:4] for c in vs[4:6]]


def char_matrix(sets):
    M = np.ones((len(sets), len(pts)), dtype=np.float32)
    for r, S in enumerate(sets):
        for v in S:
            M[r] *= pts[:, v]
    return M


def count_boolean_signs(sets):
    assert len(sets) == 16 and len(set(sets)) == 16
    M = char_matrix(sets)
    total = 0
    signs_all = np.array(list(itertools.product([1.0, -1.0], repeat=16)), dtype=np.float32)
    for start in range(0, len(signs_all), 8192):
        sg = signs_all[start:start + 8192]
        vals = sg @ M  # chunk x 2048
        ok = np.all(np.abs(vals) == 4.0, axis=1)
        total += int(ok.sum())
    return total


structures = {}
# (1) glued octahedra, shared vertex 0
structures["glued octahedra (C4+C4, different octahedra)"] = octahedron([0, 5, 1, 3, 2, 4]) + octahedron([0, 10, 6, 8, 7, 9])
# (2) delta=4 {2,2}: i=0, j=1, a=2, b=3, c=4
structures["delta=4 {2,2} L4 structure + octahedron"] = [(0,), (1,), (0, 2, 3), (0, 3, 4), (0, 2, 4), (1, 2, 3), (1, 3, 4), (1, 2, 4)] + octahedron([5, 6, 7, 8, 9, 10])
# (3) delta=4 {1,1,1,1} |N|=4: i=0, a=1, j=2, b=3, c=4
structures["delta=4 {1,1,1,1} |N|=4 structure + octahedron"] = [(0, 1), (1, 2), (2, 3), (0, 3), (0, 1, 4), (1, 2, 4), (2, 3, 4), (0, 3, 4)] + octahedron([5, 6, 7, 8, 9, 10])

for name, sets in structures.items():
    sets = [tuple(sorted(S)) for S in sets]
    # sanity: all 11 variables relevant, 16 distinct sets
    used = {v for S in sets for v in S}
    assert used == set(range(n)), (name, used)
    c = count_boolean_signs(sets)
    print(f"{name}: sign vectors giving a Boolean f: {c} of 65536")

# positive control: the checker must ACCEPT a known Boolean function with 16 unit terms.
# g(y) = (y1y2 + y1y3 + y2y4 - y3y4)/2 is a degree-2 Boolean function (4 relevant variables);
# f = (1+x0)/2 g(y) + (1-x0)/2 h(z) = (g+h)/2 + x0 (g-h)/2 is degree-3 Boolean with 16 terms +-1/4 on 9 variables.
g = [(1, 2), (1, 3), (2, 4), (3, 4)]
h = [(5, 6), (5, 7), (6, 8), (7, 8)]
ctrl = [tuple(S) for S in g] + [tuple(S) for S in h] + [tuple(sorted((0,) + S)) for S in g] + [tuple(sorted((0,) + S)) for S in h]
M = char_matrix(ctrl)
gs = np.array([1, 1, 1, -1], dtype=np.float32)
sg = np.concatenate([gs, gs, gs, -gs])  # (g+h)/2 + x0 (g-h)/2  ->  coefficients of g, h, x0 g, -x0 h
vals = sg @ M
print("positive control (9-variable branching function): Boolean =", bool(np.all(np.abs(vals) == 4.0)),
      "; sign vectors accepted over all 65536:", count_boolean_signs(ctrl), "(expected > 0)")
