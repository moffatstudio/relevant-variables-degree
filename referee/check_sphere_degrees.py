"""Referee check: degree sequences of triangulated spheres (simplicial) on 6 and 7 vertices.
A simplicial triangulation of S^2 on V vertices has 1-skeleton a maximal planar simple graph (3V-6 edges),
and conversely every maximal planar graph on V>=4 vertices is the 1-skeleton of a unique triangulation
whose faces are its triangular faces.  So enumerate maximal planar graphs by brute force.
Targets to exclude: (5,4,4,4,4,3) on 6 vertices; (6,4,4,4,4,4,4) on 7 vertices.  ((8,4^7) needs a degree-8 vertex
among 7 others: impossible trivially.)
"""
import itertools
import networkx as nx

for V in (6, 7):
    E = 3 * V - 6
    pairs = list(itertools.combinations(range(V), 2))
    seqs = {}
    count = 0
    for es in itertools.combinations(pairs, E):
        deg = [0] * V
        for a, b in es:
            deg[a] += 1
            deg[b] += 1
        if min(deg) < 3:
            continue
        g = nx.Graph()
        g.add_nodes_from(range(V))
        g.add_edges_from(es)
        if not nx.check_planarity(g)[0]:
            continue
        count += 1
        seqs.setdefault(tuple(sorted(deg, reverse=True)), 0)
        seqs[tuple(sorted(deg, reverse=True))] += 1
    print(f"V={V}: {count} labelled maximal planar graphs; degree sequences:")
    for s, c in sorted(seqs.items()):
        print("   ", s, f"(x{c} labelled)")
    target = {6: (5, 4, 4, 4, 4, 3), 7: (6, 4, 4, 4, 4, 4, 4)}[V]
    print(f"   target {target}: {'PRESENT!!' if target in seqs else 'absent (as the proof claims)'}")
