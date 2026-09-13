"""Round-2c referee checks for R3_equals_10.md (small, < 2 min).

A. Link shapes: k distinct subsets of size <= 2 of a ground set, every element in an even number of them.
   k = 4 -> expect exactly L1..L4; k = 6 with EMPTY and no singletons -> expect EMPTY + C_5 only;
   k = 6 pairs only -> C_6, C_3+C_3, bowtie; k = 8 pairs only -> 7 classes, 3 of them 2-regular (C_8, C_3+C_5, C_4+C_4).
B. The 5-cycle step (delta = 2, l = v): v has link EMPTY + C_5 on a_1..a_5, no quadratics anywhere, every other
   vertex has m = 4 with a C_4 link.  Enumerate all completions of the links of a_1..a_5 (each C_4 contains
   {v,a_{k-1}},{v,a_{k+1}}; the fourth vertex w_k ranges over the remaining 11 - 2 = 9 candidates) and check that no
   completion is consistent with every vertex having at most 4 cubics and every C_4 link being a genuine C_4.
C. Pentagon: every triangulation of a convex pentagon (2 non-crossing diagonals) has a vertex of diagonal-degree 2,
   so rim degrees (4,4,4,4,3) are impossible.  Hexagon: no triangulation (3 non-crossing diagonals) is a perfect matching.
D. Degree-sum identity for closed surfaces: 2E = 6V - 6chi; solve 4V' + c = 6V' - 6chi for the (V', chi) pairs used.
"""
import itertools
from collections import Counter
import networkx as nx


def shapes(k, ground=8, need_empty=None, singletons=None):
    subs = [()] + [(a,) for a in range(ground)] + list(itertools.combinations(range(ground), 2))
    seen = {}
    for fam in itertools.combinations(subs, k):
        cnt = Counter(a for T in fam for a in T)
        if any(v % 2 for v in cnt.values()):
            continue
        has_empty = () in fam
        nsing = sum(1 for T in fam if len(T) == 1)
        if need_empty is not None and has_empty != need_empty:
            continue
        if singletons is not None and nsing != singletons:
            continue
        # canonical form: graph on pairs + marked singletons + empty flag
        G = nx.Graph()
        for T in fam:
            if len(T) == 2:
                G.add_edge(*T)
            elif len(T) == 1:
                G.add_node(T[0], s=1)
        for v in G.nodes:
            G.nodes[v].setdefault("s", 0)
        comps = tuple(sorted(len(c) for c in nx.connected_components(G)))  # WL alone merges C_6 with C_3+C_3
        key = (has_empty, nsing, comps, nx.weisfeiler_lehman_graph_hash(G, node_attr="s", iterations=4))
        if key not in seen:
            seen[key] = (fam, G)
    return seen


def describe(fam, G):
    degs = sorted((d for _, d in G.degree()), reverse=True)
    cyc = ""
    if degs and all(d == 2 for d in degs):
        cyc = "+".join(f"C_{len(c)}" for c in sorted(nx.connected_components(G), key=len))
    return f"{[list(T) for T in fam]} degrees={degs} {cyc}"


print("=== A. link shapes (ground set of 6 suffices: k sets of size <= 2 with all counts even touch <= k elements) ===")
print("    (k = 8 pairs-only classes: not recomputed here, see round2b_out_links.txt / round2_out_links.txt)")
for k, kw in [(4, {}), (6, dict(need_empty=True, singletons=0)), (6, dict(need_empty=False, singletons=0))]:
    S = shapes(k, ground=6, **kw)
    print(f"k={k} {kw}: {len(S)} shapes")
    for fam, G in S.values():
        print("   ", describe(fam, G))

print("\n=== B. 5-cycle step ===")
# vertices: v=0, a_1..a_5 = 1..5, outside = 6..10
v = 0
A = [1, 2, 3, 4, 5]
base = {frozenset((v, A[k], A[(k + 1) % 5])) for k in range(5)}
consistent = 0
tried = 0
for ws in itertools.product(range(1, 11), repeat=5):
    ok = True
    cub = set(base)
    for k in range(5):
        ak, prev, nxt, w = A[k], A[k - 1], A[(k + 1) % 5], ws[k]
        if w in (v, ak, prev, nxt):
            ok = False
            break
        cub.add(frozenset((ak, prev, w)))
        cub.add(frozenset((ak, nxt, w)))
    if not ok:
        continue
    tried += 1
    # every a_k must have exactly 4 cubics forming a C_4 link; every other non-v vertex at most 4 cubics
    for x in range(1, 11):
        link = [tuple(sorted(S - {x})) for S in cub if x in S]
        if len(link) > 4:
            ok = False
            break
        if x in A:
            G = nx.Graph()
            G.add_edges_from(link)
            if not (len(link) == 4 and all(d == 2 for _, d in G.degree()) and nx.is_connected(G)):
                ok = False
                break
    if ok:
        consistent += 1
print(f"candidate completions with distinct w_k choices: {tried}; consistent (all a_k links C_4, all m <= 4): {consistent}")

print("\n=== C. polygon triangulations ===")


def triangulations(n):
    """all sets of n-3 non-crossing diagonals of a convex n-gon (vertices 0..n-1)"""
    diags = [(i, j) for i in range(n) for j in range(i + 2, n) if not (i == 0 and j == n - 1)]

    def cross(d1, d2):
        a, b = d1
        c, d = d2
        return (a < c < b < d) or (c < a < d < b)

    out = []
    for D in itertools.combinations(diags, n - 3):
        if all(not cross(x, y) for x, y in itertools.combinations(D, 2)):
            out.append(D)
    return out


for n in (5, 6):
    ts = triangulations(n)
    degs = sorted({tuple(sorted(Counter(a for d in D for a in d).get(i, 0) for i in range(n))) for D in ts})
    print(f"n={n}: {len(ts)} triangulations; diagonal-degree multisets: {degs}")
print("pentagon: (0,1,1,1,1) present?", (0, 1, 1, 1, 1) in
      {tuple(sorted(Counter(a for d in D for a in d).get(i, 0) for i in range(5))) for D in triangulations(5)})
print("hexagon: (1,1,1,1,1,1) present?", (1, 1, 1, 1, 1, 1) in
      {tuple(sorted(Counter(a for d in D for a in d).get(i, 0) for i in range(6))) for D in triangulations(6)})

print("\n=== D. degree sums on a closed connected triangulated surface: 2E = 6V - 6chi ===")
for chi in (2, 1, 0, -1, -2):
    for extra, label in [(0, "all deg 4"), (4, "one deg 8, rest 4"), (2, "one deg 6"), (4, "two deg 6"),
                         (2 - 2, "one 3 and one 5"), (-1, "one 3"), (1, "one 5")]:
        # 4V + extra = 6V - 6chi  ->  V = 3chi + extra/2
        Vp = 3 * chi + extra / 2
        print(f"chi={chi:2d} {label:22s} -> V' = {Vp}")
