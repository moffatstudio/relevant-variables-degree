"""Round-2b check of Lemma 1 / Lemma 2(c),(d): weighted link patterns containing a +-2.
For weights (2,), (2,1), (2,1,1), (2,1,1,1), (2,2), (2,1,1,1,1): all choices of distinct sets of size <= 2 on a
6-element ground set and all signs; test whether sum_j n_j chi_{T_j}(x) in {0,+-4} for all x.
Expected: (2,) never; (2,1) never [m=5]; (2,1,1) never [m=6]; (2,1,1,1) never [m=7]; (2,2) always [m=8];
(2,1,1,1,1) exactly when the four unit sets have empty symmetric difference and sign product -1 [m=8]."""
import itertools
from collections import Counter
import numpy as np

G = 6
SUBS = [()] + [(a,) for a in range(G)] + list(itertools.combinations(range(G), 2))
pts = np.array(list(itertools.product([1, -1], repeat=G)), dtype=np.int8)
CH = np.array([[np.prod([x[a] for a in T]) if T else 1 for x in pts] for T in SUBS], dtype=np.int8)

for w in [(2,), (2, 1), (2, 1, 1), (2, 1, 1, 1), (2, 2), (2, 1, 1, 1, 1)]:
    k = len(w)
    ok = bad = 0
    pred_ok = pred_bad = 0
    for fam in itertools.combinations(range(len(SUBS)), k):
        for perm in set(itertools.permutations(range(k))):   # which set gets which weight
            for signs in itertools.product([1, -1], repeat=k):
                vals = sum(w[perm[j]] * signs[j] * CH[fam[j]] for j in range(k))
                good = bool(np.all(np.isin(vals, [0, 4, -4])))
                # prediction for (2,1,1,1,1): unit sets have Delta = empty and sign product -1
                if w == (2, 1, 1, 1, 1):
                    units = [j for j in range(k) if w[perm[j]] == 1]
                    c = Counter(a for j in units for a in SUBS[fam[j]])
                    pred = all(v % 2 == 0 for v in c.values()) and np.prod([signs[j] for j in units]) == -1
                    if pred == good:
                        pred_ok += 1
                    else:
                        pred_bad += 1
                ok += good; bad += (not good)
    line = f"weights {w}: realisable {ok}, not {bad}"
    if w == (2, 1, 1, 1, 1):
        line += f"; prediction (Delta = empty & sign product -1) matches in {pred_ok}, mismatches {pred_bad}"
    print(line, flush=True)
