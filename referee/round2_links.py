"""Round-2 referee check: link shapes and even graphs (Lemma 1 / Lemma 2 of R3_equals_10.md).

A link at a vertex i is a family of k DISTINCT subsets T_j of size <= 2 (over the other variables) with
empty symmetric difference (every element in an even number of the T_j).  Correspondence used here:
  empty set  <-> present/absent flag (contributes nothing to the symmetric difference)
  singleton {a} <-> edge a--INF to a marked vertex INF
  pair {a,b}   <-> edge a--b
so a family of k distinct sets with Delta = empty  <->  a simple graph with k or k-1 edges (k-1 iff the
empty set is in the family) in which every non-INF vertex has even degree (then INF is even as well),
together with a choice of the marked vertex INF (or "no marked vertex" = pairs only).

Part A: even simple graphs with E = 4..8 edges up to isomorphism (brute force over edge subsets of K_8;
        8 edges with all degrees >= 2 need <= 8 vertices, so K_8 suffices).
Part B: link shapes for k = 4, 6, 8 unit terms, derived from Part A, and cross-checked for k = 4, 5, 6
        by direct brute force over families of subsets of a 6-element ground set.
"""
import itertools
from collections import Counter, defaultdict
import networkx as nx

# ---------------------------------------------------------------- Part A: even graphs
NV = 8
alledges = list(itertools.combinations(range(NV), 2))


def iso_classes(graphs):
    """graphs: list of edge-tuples. Return representatives up to isomorphism (networkx)."""
    buckets = defaultdict(list)
    reps = []
    for es in graphs:
        G = nx.Graph()
        G.add_edges_from(es)
        key = tuple(sorted((d for _, d in G.degree()), reverse=True))
        found = False
        for H in buckets[key]:
            if nx.is_isomorphic(G, H):
                found = True
                break
        if not found:
            buckets[key].append(G)
            reps.append(G)
    return reps


def describe(G):
    degs = tuple(sorted((d for _, d in G.degree()), reverse=True))
    comps = sorted(len(c) for c in nx.connected_components(G))
    if all(d == 2 for d in degs):
        return "disjoint cycles " + "+".join(f"C_{c}" for c in comps)
    return f"V={G.number_of_nodes()} E={G.number_of_edges()} degrees={degs} components={comps}"


even_graphs = {}
print("=== Part A: even simple graphs (all degrees even, no isolated vertices), up to isomorphism ===")
for E in range(3, 9):
    found = []
    for es in itertools.combinations(alledges, E):
        deg = Counter()
        for a, b in es:
            deg[a] += 1
            deg[b] += 1
        if all(v % 2 == 0 for v in deg.values()):
            found.append(es)
    reps = iso_classes(found)
    even_graphs[E] = reps
    print(f"E={E}: {len(reps)} classes")
    for G in reps:
        print("    ", describe(G))

# ---------------------------------------------------------------- Part B: link shapes
def link_shapes(k):
    """All shapes (up to relabelling) of k distinct subsets of size <= 2 with empty symmetric difference.
    Returns list of (has_empty, marked_vertex_or_None, graph) and a printable family."""
    out = []
    for has_empty in (False, True):
        E = k - 1 if has_empty else k
        for G in even_graphs[E]:
            # choice of INF: none, or one vertex per automorphism orbit
            choices = [None]
            seen = []
            for v in G.nodes():
                dup = False
                for u in seen:
                    # same orbit iff G with v marked iso to G with u marked
                    Gv = G.copy(); Gv.nodes[v]["m"] = 1
                    Gu = G.copy(); Gu.nodes[u]["m"] = 1
                    for w in Gv.nodes():
                        Gv.nodes[w].setdefault("m", 0)
                    for w in Gu.nodes():
                        Gu.nodes[w].setdefault("m", 0)
                    if nx.is_isomorphic(Gv, Gu, node_match=lambda a, b: a["m"] == b["m"]):
                        dup = True
                        break
                if not dup:
                    seen.append(v)
            choices += seen
            for inf in choices:
                fam = []
                if has_empty:
                    fam.append(())
                names = {}
                for v in sorted(G.nodes()):
                    if v != inf:
                        names[v] = "abcdefgh"[len(names)]
                for a, b in G.edges():
                    if inf in (a, b):
                        other = b if a == inf else a
                        fam.append((names[other],))
                    else:
                        fam.append(tuple(sorted((names[a], names[b]))))
                fam.sort(key=lambda T: (len(T), T))
                out.append((has_empty, inf, G, fam))
    return out


def fam_str(fam):
    return " ".join("{" + ",".join(T) + "}" for T in fam)


print()
print("=== Part B: link shapes (k distinct sets of size <= 2, empty symmetric difference) ===")
shape_strings = {}
for k in (4, 6, 8):
    shapes = link_shapes(k)
    shape_strings[k] = sorted(fam_str(f) for *_, f in shapes)
    print(f"k={k}: {len(shapes)} shapes")
    for has_empty, inf, G, fam in shapes:
        n_single = sum(1 for T in fam if len(T) == 1)
        tag = []
        if has_empty:
            tag.append("has EMPTY")
        if n_single:
            tag.append(f"{n_single} singletons")
        if not tag:
            tag.append("pairs only")
        print(f"    {fam_str(fam):50s}  [{', '.join(tag)}]")

# cross-check by brute force for k = 4, 5, 6 on ground set of 6 elements
print()
print("=== cross-check: brute force families over a 6-element ground set ===")
G6 = range(6)
sets6 = [frozenset()] + [frozenset([a]) for a in G6] + [frozenset(p) for p in itertools.combinations(G6, 2)]


def canon(fam):
    used = sorted({a for T in fam for a in T})
    best = None
    for perm in itertools.permutations(range(len(used))):
        rl = {used[j]: perm[j] for j in range(len(used))}
        key = tuple(sorted((tuple(sorted(rl[a] for a in T)) for T in fam), key=lambda T: (len(T), T)))
        if best is None or key < best:
            best = key
    return best


for k in (4, 5, 6):
    shapes = set()
    for fam in itertools.combinations(sets6, k):
        c = Counter(a for T in fam for a in T)
        if all(v % 2 == 0 for v in c.values()):
            shapes.add(canon(fam))
    strs = sorted(" ".join("{" + ",".join("abcdefgh"[a] for a in T) + "}" for T in s) for s in shapes)
    print(f"k={k}: brute force gives {len(shapes)} shapes")
    if k in shape_strings:
        print("   agrees with graph method:", sorted(strs) == sorted(shape_strings[k]))
    else:
        for s in strs:
            print("    ", s)
