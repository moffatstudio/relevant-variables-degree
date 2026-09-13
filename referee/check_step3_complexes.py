"""Referee check for Step 3 (topology-free): enumerate every 3-uniform hypergraph F on <= 12 labelled vertices
in which EVERY vertex lies in exactly 4 triples whose links (pairs S\\{i}) form a 4-cycle.
Claim to verify: every such F is a disjoint union of octahedra (so on 12 vertices: two octahedra).

Search: vertices are introduced in increasing label order (symmetry breaking: any solution can be relabelled so).
Process the smallest vertex whose link is not yet complete; extend its current partial link (a set of edges forming
paths, since it must embed in a C4) to a full C4 by adding triples i-x-y, using existing vertices or the next unused
label. Check consistency (each pair in <= 2 triples; each vertex in <= 4 triples; every partial link is a
disjoint union of paths on <= 4 vertices)."""
import itertools, sys
sys.setrecursionlimit(10000)
NMAX = 12

def link_edges(F, i):
    return [tuple(sorted(S - {i})) for S in F if i in S]

def partial_link_ok(edges):
    # must embed in a C4: <=4 vertices, degrees <=2, <=4 edges, no cycle unless it is the full C4
    deg = {}
    for a, b in edges:
        deg[a] = deg.get(a, 0) + 1; deg[b] = deg.get(b, 0) + 1
    if len(deg) > 4 or any(d > 2 for d in deg.values()) or len(edges) > 4:
        return False
    # acyclic unless complete
    parent = {v: v for v in deg}
    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]; v = parent[v]
        return v
    cyc = 0
    for a, b in edges:
        ra, rb = find(a), find(b)
        if ra == rb:
            cyc += 1
        else:
            parent[ra] = rb
    if cyc > 1: return False
    if cyc == 1 and not (len(edges) == 4 and len(deg) == 4): return False
    return True

def is_c4(edges):
    return len(edges) == 4 and partial_link_ok(edges) and len({v for e in edges for v in e}) == 4 and \
        all(sum(v in e for e in edges) == 2 for v in {v for e in edges for v in e})

def consistent(F, used):
    for v in used:
        if not partial_link_ok(link_edges(F, v)):
            return False
    for S in F:
        for p in itertools.combinations(sorted(S), 2):
            if sum(set(p) <= T for T in F) > 2:
                return False
    return True

solutions = []
def rec(F, used):
    # find smallest vertex with incomplete link
    incomplete = [v for v in sorted(used) if not is_c4(link_edges(F, v))]
    if not incomplete:
        solutions.append(frozenset(F)); return
    i = incomplete[0]
    L = link_edges(F, i)
    # candidate vertices: existing ones plus one fresh label
    fresh = max(used) + 1 if used else 0
    extra = {v for v in (fresh, fresh + 1) if v < NMAX}
    cands = sorted(used | extra)
    cands = [v for v in cands if v != i]
    # choose a new pair {x,y} to add as triple {i,x,y}; to limit branching, require it to attach to an existing
    # link edge when the link is nonempty (a C4 is connected), and require x<y with x the smallest label
    # among "new" choices handled by symmetry of fresh label only.
    for x, y in itertools.combinations(cands, 2):
        if y == fresh + 1 and x != fresh:  # labels introduced in increasing order
            continue
        S = frozenset({i, x, y})
        if S in F: continue
        if L and not ({x, y} & {v for e in L for v in e}): continue
        F2 = F | {S}
        used2 = used | {x, y}
        if len(used2) > NMAX: continue
        if not consistent(F2, used2): continue
        rec(F2, used2)

rec(frozenset(), {0})
uniq = set(solutions)
print("complete complexes found (labelled, with increasing-label introduction):", len(uniq))
from collections import Counter
def components(F):
    verts = {v for S in F for v in S}
    comp = {}; k = 0
    for v in sorted(verts):
        if v in comp: continue
        stack = [v]; comp[v] = k
        while stack:
            u = stack.pop()
            for S in F:
                if u in S:
                    for w in S:
                        if w not in comp:
                            comp[w] = k; stack.append(w)
        k += 1
    sizes = Counter(comp.values())
    return sorted(sizes.values())
summary = Counter()
for F in uniq:
    verts = {v for S in F for v in S}
    summary[(len(verts), len(F), tuple(components(F)))] += 1
for k, v in sorted(summary.items()):
    print("  vertices=%d triples=%d component sizes=%s : %d labelled complexes" % (k[0], k[1], k[2], v))
# verify each component is an octahedron: 6 vertices, 8 triples, 1-skeleton = K_{2,2,2}
def is_octahedron(F):
    verts = sorted({v for S in F for v in S})
    if len(verts) != 6 or len(F) != 8: return False
    adj = {v: set() for v in verts}
    for S in F:
        for a, b in itertools.combinations(S, 2):
            adj[a].add(b); adj[b].add(a)
    return all(len(adj[v]) == 4 for v in verts)
allok = True
for F in uniq:
    verts = {v for S in F for v in S}
    comp = {}
    # split by component
    for cs in set(components(F)):
        pass
    # simple: every vertex's component must be an octahedron
    for v in verts:
        C = {v}; stack = [v]
        while stack:
            u = stack.pop()
            for S in F:
                if u in S:
                    for w in S:
                        if w not in C: C.add(w); stack.append(w)
        FC = {S for S in F if S <= C}
        if not is_octahedron(FC):
            allok = False; print("NON-OCTAHEDRAL COMPONENT", sorted(C), sorted(map(sorted, FC)))
print("every component is an octahedron:", allok)
