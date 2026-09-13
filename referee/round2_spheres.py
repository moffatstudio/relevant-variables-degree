"""Round-2 referee check: triangulated spheres on 6 and 7 vertices and their degree sequences.

The proof (delta = 0 sub-cases) claims that no triangulated 2-sphere has degree sequence
(5,4,4,4,4,3) [6 vertices] or (6,4,4,4,4,4,4) [7 vertices] or (8,4^7) [8 vertices, trivially impossible].

Method 1 (independent of round 1's planar-graph route): enumerate closed simplicial 2-complexes
directly. A triangulated sphere on n vertices has 2n-4 faces. For n = 6: all 8-subsets of the 20 triples,
keep those in which every edge lies in 0 or 2 faces and every vertex link is a single cycle and the complex
is connected; then Euler characteristic must be 2. For n = 7 (10 faces out of 35 triples) use backtracking on
faces in lexicographic order with the edge-multiplicity <= 2 pruning.
Method 2: maximal planar graphs (3n-6 edges, planar) via networkx, as a cross-check.
"""
import itertools
from collections import Counter, defaultdict
import networkx as nx


def surface_check(faces, n):
    """Return degree sequence (sorted desc) if `faces` is a connected closed surface with chi = 2, else None."""
    edge_cnt = Counter()
    for f in faces:
        for e in itertools.combinations(f, 2):
            edge_cnt[e] += 1
    if any(c != 2 for c in edge_cnt.values()):
        return None
    # vertex links must be single cycles
    for v in range(n):
        link = nx.Graph()
        for f in faces:
            if v in f:
                a, b = [u for u in f if u != v]
                link.add_edge(a, b)
        if link.number_of_nodes() == 0:
            return None
        if any(d != 2 for _, d in link.degree()) or not nx.is_connected(link):
            return None
    G = nx.Graph()
    G.add_edges_from(edge_cnt.keys())
    if G.number_of_nodes() != n or not nx.is_connected(G):
        return None
    chi = n - len(edge_cnt) + len(faces)
    if chi != 2:
        return None
    return tuple(sorted((d for _, d in G.degree()), reverse=True))


def enumerate_spheres(n):
    triples = list(itertools.combinations(range(n), 3))
    F = 2 * n - 4
    seqs = Counter()
    count = 0
    # backtracking with edge multiplicity pruning
    edge_cnt = Counter()
    chosen = []

    def rec(start):
        nonlocal count
        if len(chosen) == F:
            s = surface_check(chosen, n)
            if s is not None:
                count += 1
                seqs[s] += 1
            return
        if F - len(chosen) > len(triples) - start:
            return
        for idx in range(start, len(triples)):
            t = triples[idx]
            es = list(itertools.combinations(t, 2))
            if any(edge_cnt[e] >= 2 for e in es):
                continue
            for e in es:
                edge_cnt[e] += 1
            chosen.append(t)
            rec(idx + 1)
            chosen.pop()
            for e in es:
                edge_cnt[e] -= 1

    rec(0)
    return count, seqs


for n in (6, 7):
    count, seqs = enumerate_spheres(n)
    print(f"n={n}: {count} labelled triangulated spheres (closed, connected, chi=2); degree sequences:")
    for s, c in sorted(seqs.items(), reverse=True):
        print(f"    {s}  x{c}")
    for target in [(5, 4, 4, 4, 4, 3), (6, 4, 4, 4, 4, 4, 4)]:
        if len(target) == n:
            print(f"   target {target}: {'PRESENT' if target in seqs else 'absent (proof claim confirmed)'}")

print()
print("cross-check: maximal planar graphs (3n-6 edges, planar) via networkx")
for n in (6, 7):
    E = 3 * n - 6
    alle = list(itertools.combinations(range(n), 2))
    seqs = Counter()
    for es in itertools.combinations(alle, E):
        G = nx.Graph()
        G.add_nodes_from(range(n))
        G.add_edges_from(es)
        if min(d for _, d in G.degree()) < 3:
            continue
        ok, _ = nx.check_planarity(G)
        if ok:
            seqs[tuple(sorted((d for _, d in G.degree()), reverse=True))] += 1
    print(f"n={n}: degree sequences of maximal planar graphs:")
    for s, c in sorted(seqs.items(), reverse=True):
        print(f"    {s}  x{c}")
