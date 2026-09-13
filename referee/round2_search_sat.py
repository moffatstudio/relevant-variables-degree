"""Round-2 referee: same structure search as round2_search.py, but with a plain CDCL SAT solver (pysat) and
blocking clauses, i.e. complete enumeration by construction.  See the docstring of round2_search.py for the facts
(F1)-(F3) that define the search space:
  H = 16 distinct sets of size 0..3 on 11 vertices, deg(i) in {4,6,8} for all i, all pair codegrees even,
  vertex 0 of maximum degree with a fixed labelled link shape.
Then every one of the 2^16 sign vectors is tested for Boolean-ness on each structure found.
"""
import itertools, sys, time
from collections import Counter
import numpy as np
from pysat.solvers import Solver
from pysat.card import ITotalizer, CardEnc, EncType
from pysat.formula import IDPool

sys.path.insert(0, ".")
from round2_search import link_shapes, boolean_sign_count, hypergraph_key, hg_iso, SETS, idx, n


def enumerate_structures_sat(d0, link, cap=500000):
    pool = IDPool()
    e = {S: pool.id(("e", S)) for S in SETS}
    clauses = []
    # total 16
    cnf = CardEnc.equals(lits=[e[S] for S in SETS], bound=16, vpool=pool, encoding=EncType.totalizer)
    clauses += cnf.clauses
    top = max(pool.top, max(abs(l) for c in cnf.clauses for l in c))
    tots = []
    # degrees in {4,6,8}, <= d0
    for i in range(n):
        lits = [e[S] for S in SETS if i in S]
        t = ITotalizer(lits=lits, ubound=9, top_id=top)
        top = t.top_id
        tots.append(t)
        clauses += t.cnf.clauses
        r = t.rhs  # r[k] true iff at least k+1 lits true
        clauses.append([r[3]])            # >= 4
        clauses.append([-r[8]])           # <= 8
        clauses.append([-r[4], r[5]])     # not exactly 5
        clauses.append([-r[6], r[7]])     # not exactly 7
        if d0 == 4:
            clauses.append([-r[4]])
        elif d0 == 6:
            clauses.append([-r[6]])
    # even codegrees
    for i, x in itertools.combinations(range(n), 2):
        lits = [e[S] for S in SETS if i in S and x in S]  # 10 literals
        t = ITotalizer(lits=lits, ubound=10, top_id=top)
        top = t.top_id
        tots.append(t)
        clauses += t.cnf.clauses
        r = t.rhs
        for odd in (1, 3, 5, 7, 9):
            clauses.append([-r[odd - 1], r[odd]])  # not exactly `odd`
    # fixed link of vertex 0
    linkset = {tuple(sorted((0,) + T)) for T in link}
    for S in SETS:
        if 0 in S:
            clauses.append([e[S]] if S in linkset else [-e[S]])
    sols = []
    with Solver(name="cadical153", bootstrap_with=clauses) as s:
        while s.solve():
            model = set(l for l in s.get_model() if l > 0)
            H = tuple(S for S in SETS if e[S] in model)
            assert len(H) == 16
            sols.append(H)
            s.add_clause([-e[S] for S in H])
            if len(sols) >= cap:
                break
    return sols


if __name__ == "__main__":
    t0 = time.time()
    grand_total = 0
    boolean_found = 0
    iso_reps = []
    for d0 in (4, 6, 8):
        shapes = link_shapes(d0)
        print(f"=== vertex 0 of maximum degree d0 = {d0}: {len(shapes)} link shapes ===", flush=True)
        for link in shapes:
            desc = " ".join("{" + ",".join(map(str, T)) + "}" for T in link)
            t1 = time.time()
            sols = enumerate_structures_sat(d0, link)
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
            print(f"  link(0) = {desc:55s} structures={len(sols):6d} new iso classes={new_iso} boolean sign vectors={nb}  ({time.time()-t1:.1f}s)", flush=True)
    print()
    print(f"TOTAL labelled structures (with the symmetry breaking): {grand_total}")
    print(f"isomorphism classes of structures satisfying (F1)-(F3): {len(iso_reps)}")
    for key, H in iso_reps:
        degs = Counter(v for S in H for v in S)
        prof = dict(Counter(len(S) for S in H))
        print("   sizes", prof, "degree sequence", tuple(sorted(degs.values(), reverse=True)), "sets:", H)
    print(f"Boolean sign vectors over all structures: {boolean_found}   (expected 0)")
    print(f"time {time.time() - t0:.1f}s")
