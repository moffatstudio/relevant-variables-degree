"""Round-2b referee check (independent of round2_links.py's even-graph construction).

Claim checked (Lemma 2(a),(b),(c) sign-free part): the families of k DISTINCT subsets of size <= 2 of a ground
set, with EMPTY symmetric difference (every element in an even number of members), are, up to relabelling:
  k = 4: exactly L1 = C_4 of pairs, L2 = {0,a,b,ab}, L3 = {a,b,ac,bc}, L4 = {0,ab,bc,ac}      (4 shapes)
  k = 5: (used for the delta=2, m_l=6 link: 0 + five pairs  ->  C_5)                          (4 shapes)
  k = 6: pairs-only shapes are exactly C_6, C_3+C_3, bowtie                                   (9 shapes)
  k = 8: pairs-only shapes: 7; the 2-regular ones are exactly C_8, C_3+C_5, C_4+C_4          (36 shapes)

Method: direct brute force over families of subsets of an 8-element ground set (37 subsets of size <= 2).
Ground set of 8 suffices: every used element occurs >= 2 times, so <= k elements are used, and k <= 8.
For k members we enumerate (k-1)-subsets, XOR their incidence masks; the last member is forced (mask = XOR),
and to count each family once we require it to have the largest index.  Isomorphism classes via networkx on the
bipartite incidence graph (elements / members, with member size as a node attribute), bucketed by an invariant.
"""
import itertools, time
from collections import Counter, defaultdict
import networkx as nx

G = 8
SUBS = [()] + [(a,) for a in range(G)] + list(itertools.combinations(range(G), 2))
MASK = [sum(1 << a for a in T) for T in SUBS]
IDX = {m: t for t, m in enumerate(MASK)}   # mask -> index (all masks distinct)


def families(k):
    """all k-families of distinct members of SUBS with empty symmetric difference, each exactly once"""
    out = []
    for comb in itertools.combinations(range(len(SUBS)), k - 1):
        x = 0
        for c in comb:
            x ^= MASK[c]
        t = IDX.get(x)
        if t is not None and t > comb[-1]:
            out.append(comb + (t,))
    return out


def inc_graph(fam):
    Gr = nx.Graph()
    for j, t in enumerate(fam):
        Gr.add_node(("m", j), t=10 + len(SUBS[t]))
        for a in SUBS[t]:
            Gr.add_node(("e", a), t=0)
            Gr.add_edge(("m", j), ("e", a))
    if not Gr.number_of_nodes():
        Gr.add_node("dummy", t=99)
    return Gr


def invariant(fam):
    sizes = tuple(sorted(len(SUBS[t]) for t in fam))
    deg = Counter(); sing = Counter()
    for t in fam:
        for a in SUBS[t]:
            deg[a] += 1
            if len(SUBS[t]) == 1:
                sing[a] += 1
    # per element: (degree, is-singleton, sorted degrees of pair-neighbours)
    nb = defaultdict(list)
    for t in fam:
        T = SUBS[t]
        if len(T) == 2:
            nb[T[0]].append(T[1]); nb[T[1]].append(T[0])
    per = tuple(sorted((deg[a], sing[a], tuple(sorted(deg[b] for b in nb[a]))) for a in deg))
    return sizes, per


def classes(fams):
    reps = defaultdict(list)   # invariant -> list of (fam, graph)
    for fam in fams:
        inv = invariant(fam)
        g = inc_graph(fam)
        if not any(nx.is_isomorphic(g, h, node_match=lambda a, b: a["t"] == b["t"]) for _, h in reps[inv]):
            reps[inv].append((fam, g))
    return [fam for lst in reps.values() for fam, _ in lst]


def show(fam):
    names = "abcdefgh"
    return " ".join("{" + ",".join(names[a] for a in SUBS[t]) + "}" for t in sorted(fam, key=lambda t: (len(SUBS[t]), SUBS[t])))


def pairs_only_type(fam):
    """for pairs-only families: cycle structure if 2-regular, else degree sequence"""
    Gr = nx.Graph(); Gr.add_edges_from(SUBS[t] for t in fam)
    degs = sorted((d for _, d in Gr.degree()), reverse=True)
    if all(d == 2 for d in degs):
        return "2-regular: " + "+".join(f"C_{len(c)}" for c in sorted(nx.connected_components(Gr), key=len))
    return f"degrees {tuple(degs)}"


if __name__ == "__main__":
    t0 = time.time()
    for k in (4, 5, 6, 8):
        fams = families(k)
        reps = classes(fams)
        print(f"k = {k}: {len(fams)} labelled families on 8 elements, {len(reps)} shapes up to relabelling  ({time.time()-t0:.0f}s)")
        po = 0
        for fam in sorted(reps, key=lambda f: (sum(1 for t in f if len(SUBS[t]) == 0), sum(1 for t in f if len(SUBS[t]) == 1), show(f))):
            n0 = sum(1 for t in fam if len(SUBS[t]) == 0)
            n1 = sum(1 for t in fam if len(SUBS[t]) == 1)
            tag = ("has EMPTY, " if n0 else "") + (f"{n1} singletons" if n1 else "pairs only")
            extra = ""
            if n0 == 0 and n1 == 0:
                po += 1; extra = "   <- " + pairs_only_type(fam)
            if n0 == 1 and n1 == 0:
                extra = "   <- EMPTY + " + pairs_only_type([t for t in fam if len(SUBS[t]) == 2])
            print(f"    {show(fam):52s} [{tag}]{extra}")
        print(f"    pairs-only shapes (= even simple graphs with {k} edges): {po}")
        print()
    print(f"total time {time.time()-t0:.0f}s")
