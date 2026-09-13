"""Round-2b cross-check: re-solve the d0 = 4 cells (r = 2..6) of round2b_search.py's model with OR-tools CP-SAT
(second solver, same constraints, same symmetry breaking) and compare the labelled solution SETS with pysat's."""
import sys, time
sys.path.insert(0, __file__.rsplit("\\", 1)[0] if "\\" in __file__ else ".")
import round2b_search as R

if __name__ == "__main__":
    for r in (2, 3, 4, 5, 6):
        t = time.time()
        a = set(R.solve_cpsat(4, r))
        t1 = time.time() - t
        b = set(R.solve_pysat(4, r))
        t2 = time.time() - t - t1
        print(f"d0=4 r={r}: CP-SAT {len(a)} ({t1:.0f}s)  pysat {len(b)} ({t2:.0f}s)  identical sets: {a == b}", flush=True)
