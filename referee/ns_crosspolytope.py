"""Sanity checks (ii),(iii) for NS_never_tight.md.

(ii) Single cross-polytope boundary, coefficient 2^{-(d-1)}, all sign patterns:
     d=3 octahedron (6 vertices, 8 facets, coeff 1/4, 2^8 patterns)
     d=4 16-cell   (8 vertices, 16 facets, coeff 1/8, 2^16 patterns)
     -> never Boolean.  (Parseval already forbids it: weight 2^d * 2^{-2(d-1)} = 2^{2-d}.)
(iii) d=2 square with signs (+,+,+,-), coeff 1/2 -> Boolean.
Also: the closure argument for d=3 — every 3-uniform hypergraph on <= 12 vertices in
which every vertex has exactly 4 terms whose link is a 4-cycle is a disjoint union of
octahedron boundaries (checked by exhaustive extension from a fixed vertex link).
"""
import itertools
import numpy as np

def facets(d):
    # pairs (2k, 2k+1), k = 0..d-1 ; facets choose one from each pair
    return [tuple(2 * k + b[k] for k in range(d)) for b in itertools.product([0, 1], repeat=d)]

def check_single(d):
    F = facets(d)
    nv = 2 * d
    pts = np.array(list(itertools.product([1, -1], repeat=nv)), dtype=np.int64)
    rows = np.stack([np.prod(pts[:, list(S)], axis=1) for S in F])  # 2^d x 2^{2d}
    nF = len(F)
    coeff = 2.0 ** (-(d - 1))
    signs = np.array(list(itertools.product([1, -1], repeat=nF)), dtype=np.int64)
    vals = signs @ rows  # patterns x points  (integer, then times coeff)
    target = 2 ** (d - 1)
    boolean = np.all((vals == target) | (vals == -target), axis=1)
    nb = int(boolean.sum())
    print(f"d={d}: {nF} facets, {signs.shape[0]} sign patterns, Boolean patterns: {nb}")
    if nb:
        print("   example:", signs[np.nonzero(boolean)[0][0]])
    return nb

def check_square():
    # variables x1..x4 ; edges 12,13,24,34 ; f = (x1x2 + x1x3 + x2x4 - x3x4)/2
    pts = np.array(list(itertools.product([1, -1], repeat=4)))
    f = (pts[:, 0] * pts[:, 1] + pts[:, 0] * pts[:, 2] + pts[:, 1] * pts[:, 3] - pts[:, 2] * pts[:, 3]) / 2
    print("d=2 square (+,+,+,-): values", sorted(set(f.tolist())))
    return set(f.tolist()) == {-1.0, 1.0}

def is_c4(edges):
    """edges: set of frozenset pairs; is it exactly a 4-cycle graph?"""
    if len(edges) != 4:
        return False
    verts = set()
    for e in edges:
        verts |= e
    if len(verts) != 4:
        return False
    deg = {v: 0 for v in verts}
    for e in edges:
        for v in e:
            deg[v] += 1
    return all(x == 2 for x in deg.values())

def closure_d3(maxv=12):
    """Exhaustively build connected 3-uniform hypergraphs where every vertex has exactly 4
    terms forming a C4 link, starting from vertex 0 with link {1,2},{1,3},{4,2},{4,3}
    (pairs {1,4},{2,3}). Report every completed connected component."""
    results = set()
    start = [frozenset({0, 1, 2}), frozenset({0, 1, 3}), frozenset({0, 4, 2}), frozenset({0, 4, 3})]

    def link(H, v):
        return {frozenset(S - {v}) for S in H if v in S}

    def rec(H, nverts):
        # find a vertex with fewer than 4 terms
        counts = {}
        for S in H:
            for v in S:
                counts[v] = counts.get(v, 0) + 1
        for v, c in counts.items():
            if c > 4:
                return
            L = link(H, v)
            # partial link must be a subgraph of some C4 : degrees <= 2, no triangle etc. (weak prune)
            deg = {}
            for e in L:
                for u in e:
                    deg[u] = deg.get(u, 0) + 1
            if any(x > 2 for x in deg.values()):
                return
            if len(set().union(*L)) > 4:
                return
        incomplete = [v for v, c in counts.items() if c < 4]
        if not incomplete:
            comp = frozenset(H)
            results.add((len(counts), len(H)))
            return
        v = min(incomplete)
        L = link(H, v)
        Lverts = set().union(*L)
        # candidate new terms {v,a,b}: a,b existing or one new vertex (at most 1 new at a time)
        cands = list(range(nverts)) + ([nverts] if nverts < maxv else [])
        for a, b in itertools.combinations(cands, 2):
            if a == v or b == v:
                continue
            S = frozenset({v, a, b})
            if S in H:
                continue
            e = frozenset({a, b})
            newL = L | {e}
            # must be extendable to a C4 on <= 4 vertices
            if len(set().union(*newL)) > 4:
                continue
            deg = {}
            for ee in newL:
                for u in ee:
                    deg[u] = deg.get(u, 0) + 1
            if any(x > 2 for x in deg.values()):
                continue
            if len(newL) == 4 and not is_c4(newL):
                continue
            # symmetry: new vertex only if it is exactly nverts
            nv2 = max(nverts, a + 1, b + 1)
            rec(H + [S], nv2)

    rec(start, 5)
    print("d=3 closure: completed components (vertices, terms):", sorted(results))
    return results

if __name__ == "__main__":
    ok3 = check_single(3) == 0
    ok4 = check_single(4) == 0
    ok2 = check_square()
    res = closure_d3()
    print("(ii) single octahedron never Boolean:", ok3)
    print("(ii) single 16-cell never Boolean:", ok4)
    print("(iii) d=2 square Boolean:", ok2)
    print("closure d=3 only octahedron:", res == {(6, 8)})
