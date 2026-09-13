"""Round-2 referee: independent exhaustive search for the 11-variable case, at the level of term STRUCTURES.

Facts used (each re-derived by the referee, see REPORT_r3_round2.md):
  (F1) n_S := 4 f^(S) is an integer, sum n_S^2 = 16, and m_i := sum_{S ∋ i} n_S^2 = 16 Inf_i(f) in {4,6,8}
       for all 11 relevant variables (Lemma 1).
  (F2) A term with |n_S| = 2 forces m = 8 at each of its vertices; sum_i m_i <= 48 with eleven m_i >= 4 allows at
       most ONE vertex with m = 8; so a +-2 term would have |S| <= 1, i.e. constant or linear, contributing
       12 or 8 > 4 to delta = 48 - sum m_i.  Hence ALL 16 terms have n_S = +-1: the support is a hypergraph H
       of 16 distinct sets of size 0..3 on 11 vertices with vertex degrees deg(i) = m_i in {4,6,8}.
  (F3) For every vertex i, 4 D_i f = sum_{S ∋ i} eps_S chi_{S\i} takes values in {0,+-4}. With all |n| = 1 this
       forces prod_{S ∋ i} eps_S chi_{S \ i} == const, i.e. every x != i lies in an even number of the S ∋ i:
       all pair codegrees lambda_{ix} = #{S in H : i, x in S} are EVEN; and prod eps = +1 (m = 4, 8), -1 (m = 6).
Search: enumerate ALL such hypergraphs H (CP-SAT, complete enumeration) with the symmetry breaking
  "vertex 0 has maximum degree and its link is a fixed labelled representative of one of the possible link shapes"
  (shape list generated here by the even-graph method, cross-checked in round2_links.py),
then for each H check every sign vector (all 2^16) for Boolean-ness. Expected: no Boolean f.
Note the search does NOT use anything from the case analysis of the proof beyond (F1)-(F3).
"""
import itertools, sys, time
from collections import Counter, defaultdict
import numpy as np
import networkx as nx
from ortools.sat.python import cp_model

n = 11
SETS = [tuple(c) for k in range(0, 4) for c in itertools.combinations(range(n), k)]
idx = {S: t for t, S in enumerate(SETS)}
pts = np.array(list(itertools.product([1, -1], repeat=n)), dtype=np.int8)

# ------------------------------------------------------------------ link shapes (even-graph method)
def even_graphs(E, NV=8):
    alle = list(itertools.combinations(range(NV), 2))
    masks = [(1 << a) | (1 << b) for a, b in alle]
    found = []
    for comb in itertools.combinations(range(len(alle)), E):
        par = 0
        for c in comb:
            par ^= masks[c]
        if par == 0:
            found.append([alle[c] for c in comb])
    reps = []
    buckets = defaultdict(list)
    for es in found:
        G = nx.Graph(); G.add_edges_from(es)
        key = tuple(sorted((d for _, d in G.degree()), reverse=True))
        if not any(nx.is_isomorphic(G, H) for H in buckets[key]):
            buckets[key].append(G); reps.append(G)
    return reps


def marked_orbits(G):
    reps = []
    for v in G.nodes():
        dup = False
        for u in reps:
            Gv = G.copy(); Gu = G.copy()
            for w in G.nodes():
                Gv.nodes[w]["m"] = int(w == v); Gu.nodes[w]["m"] = int(w == u)
            if nx.is_isomorphic(Gv, Gu, node_match=lambda a, b: a["m"] == b["m"]):
                dup = True; break
        if not dup:
            reps.append(v)
    return reps


def link_shapes(k):
    """families of k distinct subsets of {1..} (size <= 2) with empty symmetric difference, one per iso class,
    realised on the concrete vertex labels 1, 2, ..."""
    out = []
    for has_empty in (False, True):
        E = k - 1 if has_empty else k
        for G in even_graphs(E):
            for inf in [None] + marked_orbits(G):
                fam = [()] if has_empty else []
                lab = {}
                for v in sorted(G.nodes()):
                    if v != inf:
                        lab[v] = len(lab) + 1
                for a, b in G.edges():
                    if inf in (a, b):
                        fam.append((lab[b if a == inf else a],))
                    else:
                        fam.append(tuple(sorted((lab[a], lab[b]))))
                out.append(sorted(fam, key=lambda T: (len(T), T)))
    return out


# ------------------------------------------------------------------ sign check
def boolean_sign_count(H):
    M = np.ones((16, len(pts)), dtype=np.float32)
    for r, S in enumerate(H):
        for v in S:
            M[r] *= pts[:, v]
    total = 0
    for start in range(0, 65536, 8192):
        sg = SIGNS[start:start + 8192]
        vals = sg @ M
        total += int(np.all(np.abs(vals) == 4.0, axis=1).sum())
    return total


SIGNS = np.array(list(itertools.product([1.0, -1.0], repeat=16)), dtype=np.float32)


# ------------------------------------------------------------------ CP-SAT enumeration
class Collector(cp_model.CpSolverSolutionCallback):
    def __init__(self, e, cap):
        super().__init__()
        self.e = e; self.sols = []; self.cap = cap

    def on_solution_callback(self):
        H = tuple(S for S in SETS if self.Value(self.e[idx[S]]))
        self.sols.append(H)
        if len(self.sols) >= self.cap:
            self.StopSearch()


def enumerate_structures(d0, link, cap=200000):
    m = cp_model.CpModel()
    e = [m.NewBoolVar(f"e{t}") for t in range(len(SETS))]
    m.Add(sum(e) == 16)
    deg = []
    for i in range(n):
        d = m.NewIntVarFromDomain(cp_model.Domain.FromValues([4, 6, 8]), f"d{i}")
        m.Add(d == sum(e[idx[S]] for S in SETS if i in S))
        deg.append(d)
    for i in range(1, n):
        m.Add(deg[i] <= deg[0])
    m.Add(deg[0] == d0)
    for i, x in itertools.combinations(range(n), 2):
        kk = m.NewIntVar(0, 5, f"k{i}_{x}")
        m.Add(sum(e[idx[S]] for S in SETS if i in S and x in S) == 2 * kk)
    linkset = {tuple(sorted((0,) + T)) for T in link}
    for S in SETS:
        if 0 in S:
            m.Add(e[idx[S]] == (1 if S in linkset else 0))
    solver = cp_model.CpSolver()
    solver.parameters.enumerate_all_solutions = True
    solver.parameters.num_workers = 1
    solver.parameters.keep_all_feasible_solutions_in_presolve = True
    col = Collector(e, cap)
    st = solver.Solve(m, col)
    return solver.StatusName(st), col.sols


def hypergraph_key(H):
    """cheap invariant for grouping: sorted (deg, sorted codegree multiset) per vertex + size profile"""
    degs = Counter(); co = Counter()
    for S in H:
        for v in S:
            degs[v] += 1
        for p in itertools.combinations(S, 2):
            co[p] += 1
    prof = tuple(sorted(Counter(len(S) for S in H).items()))
    per_v = []
    for v in range(n):
        cs = tuple(sorted(co[tuple(sorted((v, x)))] for x in range(n) if x != v))
        per_v.append((degs[v], cs))
    return prof, tuple(sorted(per_v))


def hg_iso(H1, H2):
    """exact isomorphism test via bipartite incidence graphs"""
    def big(H):
        G = nx.Graph()
        for v in range(n):
            G.add_node(("v", v), t=0)
        for j, S in enumerate(H):
            G.add_node(("s", j), t=1 + len(S))
            for v in S:
                G.add_edge(("s", j), ("v", v))
        return G
    return nx.is_isomorphic(big(H1), big(H2), node_match=lambda a, b: a["t"] == b["t"])


if __name__ == "__main__":
    t0 = time.time()
    grand_total = 0
    boolean_found = 0
    iso_reps = []  # (key, H)
    for d0 in (4, 6, 8):
        shapes = link_shapes(d0)
        print(f"=== vertex 0 of maximum degree d0 = {d0}: {len(shapes)} link shapes ===", flush=True)
        for link in shapes:
            desc = " ".join("{" + ",".join(map(str, T)) + "}" for T in link)
            st, sols = enumerate_structures(d0, link)
            grand_total += len(sols)
            nb = 0
            new_iso = 0
            for H in sols:
                key = hypergraph_key(H)
                if not any(k == key and hg_iso(H, H2) for k, H2 in iso_reps):
                    iso_reps.append((key, H)); new_iso += 1
                c = boolean_sign_count(H)
                if c:
                    nb += c
                    print("   !!! BOOLEAN FUNCTION FOUND, structure:", H, "signs:", c, flush=True)
            boolean_found += nb
            print(f"  link(0) = {desc:55s} status={st:10s} structures={len(sols):6d} new iso classes={new_iso} boolean sign vectors={nb}", flush=True)
    print()
    print(f"TOTAL labelled structures (with the symmetry breaking): {grand_total}")
    print(f"isomorphism classes of structures satisfying (F1)-(F3): {len(iso_reps)}")
    for key, H in iso_reps:
        degs = Counter(v for S in H for v in S)
        prof = dict(Counter(len(S) for S in H))
        print("   sizes", prof, "degree sequence", tuple(sorted(degs.values(), reverse=True)), "sets:", H)
    print(f"Boolean sign vectors over all structures: {boolean_found}   (expected 0)")
    print(f"time {time.time() - t0:.1f}s")
