"""Referee check: simple graphs with all degrees even and exactly E edges, E in {4,5,6,8},
up to isomorphism.  (Links of m=4,5?,6,8 vertices in the homogeneous case.)
A graph with E edges and all degrees >= 2 has at most E vertices, so a ground set of E vertices suffices.
"""
import itertools
import networkx as nx


def even_graphs(E):
    V = E
    pairs = list(itertools.combinations(range(V), 2))
    found = []
    for es in itertools.combinations(pairs, E):
        deg = [0] * V
        for a, b in es:
            deg[a] += 1
            deg[b] += 1
        if any(d % 2 for d in deg):
            continue
        g = nx.Graph()
        g.add_edges_from(es)
        if not any(nx.is_isomorphic(g, h) for h in found):
            found.append(g)
    return found


def describe(g):
    comps = []
    for c in nx.connected_components(g):
        h = g.subgraph(c)
        degs = sorted((d for _, d in h.degree()), reverse=True)
        n, m = h.number_of_nodes(), h.number_of_edges()
        if all(d == 2 for d in degs):
            comps.append(f"C_{n}")
        else:
            comps.append(f"({n} vertices, {m} edges, degrees {degs})")
    return " + ".join(sorted(comps))


for E in (4, 5, 6, 8):
    gs = even_graphs(E)
    print(f"E={E}: {len(gs)} even simple graphs up to isomorphism")
    for g in gs:
        print("   ", describe(g))
