"""Round-2b referee: independent exhaustive search of 11-variable term STRUCTURES (pysat, CDCL + blocking clauses).

Independent of round2_search.py in three ways: different solver (CaDiCaL via pysat, complete enumeration by
blocking clauses), different encodings (XOR parity chains for evenness, sequential-counter cardinalities for the
bounds), and a different symmetry breaking that does NOT use the link-shape list:
    vertex 0 has maximum degree d0, and its neighbourhood {x : codeg(0,x) > 0} is exactly {1, ..., r}.
Every hypergraph can be relabelled to satisfy this (pick a max-degree vertex, then list its neighbours first).

Facts assumed (each re-derived in REPORT_r3_round2.md from E1-E2 of FINITE_STATEMENT.md; see also the proof's Lemma 1/2(d)):
  (F1) n_S = 4 f^(S) integer, sum n_S^2 = 16, m_i = sum_{S ∋ i} n_S^2 in {4,6,8} for every relevant i.
  (F2) all 16 terms have n_S = +-1  (a +-2 term forces m = 8 at all its vertices; at most one m_i = 8; a constant or
       linear +-2 has weight 12 or 8 below the top level, but 48 - sum m_i <= 4).  So the support H is a set of 16
       distinct subsets of [11] of size 0..3 with vertex degrees m_i in {4,6,8}.
  (F3) 4 D_i f = sum_{S ∋ i} eps_S chi_{S \ i} in {0,+-4}: a sum of m_i (4, 6 or 8) values +-1 lies in {0,+-4} iff the
       number of -1's has a fixed parity, so prod_S eps_S chi_{S \ i} is constant, so every x != i lies in an even number
       of the S ∋ i: all pair codegrees are even.
For every structure found, all 2^16 sign vectors are tested for f^2 == 1 on all 2048 points.
Usage: python round2b_search.py [--cpsat]  (the flag re-runs the same model with OR-tools CP-SAT as a second solver)
"""
import itertools, sys, time
from collections import Counter, defaultdict
import numpy as np
import networkx as nx

n = 11
SETS = [tuple(c) for k in range(0, 4) for c in itertools.combinations(range(n), k)]
idx = {S: t for t, S in enumerate(SETS)}
NS = len(SETS)  # 232
pts = np.array(list(itertools.product([1, -1], repeat=n)), dtype=np.int8)
SIGNS = np.array(list(itertools.product([1.0, -1.0], repeat=16)), dtype=np.float32)


# ------------------------------------------------------------------ pysat model
def solve_pysat(d0, r, cap=10**6):
    from pysat.solvers import Solver
    from pysat.card import CardEnc, EncType
    from pysat.formula import IDPool
    pool = IDPool(start_from=NS + 1)
    e = {S: idx[S] + 1 for S in SETS}          # variables 1..232
    cls = []

    def parity_even(lits):
        """XOR chain: p_j <-> p_{j-1} xor l_j, p_0 = false, p_last = false"""
        prev = None
        for l in lits:
            if prev is None:
                prev = l
                continue
            p = pool.id()
            # p <-> prev xor l
            cls.extend([[-p, prev, l], [-p, -prev, -l], [p, -prev, l], [p, prev, -l]])
            prev = p
        if prev is not None:
            cls.append([-prev])

    # total 16
    cls += CardEnc.equals(lits=[e[S] for S in SETS], bound=16, vpool=pool, encoding=EncType.seqcounter).clauses
    # degrees: in [4, d0], even  -> in {4,6,8} ∩ [4, d0]; vertex 0 exactly d0
    for i in range(n):
        lits = [e[S] for S in SETS if i in S]
        cls += CardEnc.atleast(lits=lits, bound=4, vpool=pool, encoding=EncType.seqcounter).clauses
        cls += CardEnc.atmost(lits=lits, bound=d0, vpool=pool, encoding=EncType.seqcounter).clauses
        parity_even(lits)
        if i == 0:
            cls += CardEnc.atleast(lits=lits, bound=d0, vpool=pool, encoding=EncType.seqcounter).clauses
    # codegrees even; neighbourhood of 0 is {1..r}
    for i, x in itertools.combinations(range(n), 2):
        lits = [e[S] for S in SETS if i in S and x in S]
        parity_even(lits)
        if i == 0:
            if x <= r:
                cls.append(list(lits))              # at least one common set
            else:
                cls.extend([[-l] for l in lits])    # none
    sols = []
    with Solver(name="cadical153", bootstrap_with=cls) as s:
        while s.solve():
            model = s.get_model()
            H = tuple(S for S in SETS if model[e[S] - 1] > 0)
            assert len(H) == 16, len(H)
            sols.append(H)
            s.add_clause([-e[S] for S in H])
            if len(sols) >= cap:
                break
    return sols


# ------------------------------------------------------------------ CP-SAT model (second solver, same constraints)
def solve_cpsat(d0, r, cap=10**6):
    from ortools.sat.python import cp_model
    m = cp_model.CpModel()
    e = [m.NewBoolVar(f"e{t}") for t in range(NS)]
    m.Add(sum(e) == 16)
    for i in range(n):
        lits = [e[idx[S]] for S in SETS if i in S]
        d = m.NewIntVar(4, d0, f"d{i}")
        m.Add(d == sum(lits))
        h = m.NewIntVar(2, 4, f"h{i}")
        m.Add(d == 2 * h)
        if i == 0:
            m.Add(d == d0)
    for i, x in itertools.combinations(range(n), 2):
        lits = [e[idx[S]] for S in SETS if i in S and x in S]
        c = m.NewIntVar(0, 5, f"c{i}_{x}")
        m.Add(sum(lits) == 2 * c)
        if i == 0:
            if x <= r:
                m.Add(c >= 1)
            else:
                m.Add(c == 0)

    class Col(cp_model.CpSolverSolutionCallback):
        def __init__(self):
            super().__init__(); self.sols = []

        def on_solution_callback(self):
            self.sols.append(tuple(S for S in SETS if self.Value(e[idx[S]])))
            if len(self.sols) >= cap:
                self.StopSearch()

    solver = cp_model.CpSolver()
    solver.parameters.enumerate_all_solutions = True
    solver.parameters.num_workers = 1
    col = Col()
    st = solver.Solve(m, col)
    assert solver.StatusName(st) in ("OPTIMAL", "FEASIBLE", "INFEASIBLE"), solver.StatusName(st)
    return col.sols


# ------------------------------------------------------------------ analysis helpers
def boolean_sign_count(H):
    M = np.ones((16, len(pts)), dtype=np.float32)
    for row, S in enumerate(H):
        for v in S:
            M[row] *= pts[:, v]
    total = 0
    for start in range(0, 65536, 8192):
        vals = SIGNS[start:start + 8192] @ M
        total += int(np.all(np.abs(vals) == 4.0, axis=1).sum())
    return total


def inc_graph(H):
    Gr = nx.Graph()
    for v in range(n):
        Gr.add_node(("v", v), t=0)
    for j, S in enumerate(H):
        Gr.add_node(("s", j), t=10 + len(S))
        for v in S:
            Gr.add_edge(("s", j), ("v", v))
    return Gr


def invariant(H):
    deg = Counter(); co = Counter()
    for S in H:
        for v in S:
            deg[v] += 1
        for p in itertools.combinations(S, 2):
            co[p] += 1
    prof = tuple(sorted(Counter(len(S) for S in H).items()))
    per = tuple(sorted((deg[v], tuple(sorted(co[tuple(sorted((v, x)))] for x in range(n) if x != v))) for v in range(n)))
    return prof, per


def describe(H):
    deg = Counter(v for S in H for v in S)
    return f"sizes {dict(sorted(Counter(len(S) for S in H).items()))} degrees {tuple(sorted(deg.values(), reverse=True))} sets {H}"


if __name__ == "__main__":
    use_cpsat = "--cpsat" in sys.argv
    solve = solve_cpsat if use_cpsat else solve_pysat
    print("solver:", "CP-SAT" if use_cpsat else "pysat/CaDiCaL", flush=True)
    t0 = time.time()
    reps = defaultdict(list)  # invariant -> [(H, graph)]
    grand = 0; nbool = 0
    per_class_signs = {}
    for d0 in (4, 6, 8):
        for r in range(0, 11):
            t1 = time.time()
            sols = solve(d0, r)
            grand += len(sols)
            new = 0
            for H in sols:
                inv = invariant(H)
                g = inc_graph(H)
                if not any(nx.is_isomorphic(g, h, node_match=lambda a, b: a["t"] == b["t"]) for _, h in reps[inv]):
                    reps[inv].append((H, g)); new += 1
                c = boolean_sign_count(H)
                nbool += c
                if c:
                    print("   !!! BOOLEAN FUNCTION FOUND:", H, "sign vectors:", c, flush=True)
            if sols or r <= 8:
                print(f"  d0={d0} |N(0)|={r:2d}: structures={len(sols):5d} new iso classes={new} boolean sign vectors={sum(boolean_sign_count(H) for H in sols) if sols else 0}  ({time.time()-t1:.1f}s)", flush=True)
    print()
    print(f"TOTAL labelled structures (with symmetry breaking): {grand}")
    allreps = [H for lst in reps.values() for H, _ in lst]
    print(f"isomorphism classes of structures satisfying (F1)-(F3): {len(allreps)}")
    for H in allreps:
        print("   ", describe(H))
    print(f"Boolean sign vectors over all structures (2^16 each): {nbool}   (expected 0)")
    print(f"time {time.time()-t0:.1f}s")
