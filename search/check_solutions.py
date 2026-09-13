"""
Independent verification and orbit counting for solutions printed by r3search.

Each SOL line lists terms "i,j,k:c" (1-based variables, integer coefficient n_S).  For every line we
re-check, from scratch and in Python:
  (i)   sum n_S^2 == 16,
  (ii)  (1/4) sum n_S chi_S(x) in {+1,-1} at all 2^n points,
  (iii) every variable 1..n occurs in a term with nonzero coefficient, and |S| <= 3.
Then solutions are reduced to a canonical form under the symmetry group of E3
(permutations of variables x negations of variables x global sign) and the number of orbits is reported.

Canonical form: vertices are partitioned by an isomorphism-invariant colouring (iteratively refined);
we take the minimum over all permutations that list the colour classes in sorted order of the
lexicographically smallest sign-normalised coefficient vector (sign-normalisation = greedy lex-min over
the 2^(n+1) sign flips, computed exactly by GF(2) elimination).

Usage: python check_solutions.py n solutions.txt [--xi3]
"""
import sys, itertools
import numpy as np

def parse(path):
    sols = []
    for line in open(path):
        if not line.startswith("SOL"):
            continue
        terms = {}
        for tok in line.split()[1:]:
            S, c = tok.split(":")
            S = () if S in ("", "e") else tuple(int(a) - 1 for a in S.split(","))
            terms[S] = int(c)
        sols.append(terms)
    return sols

def verify(terms, n):
    if sum(c * c for c in terms.values()) != 16:
        return "mass != 16"
    if any(len(S) > 3 for S in terms):
        return "degree > 3"
    rel = set(i for S in terms for i in S if terms[S])
    if rel != set(range(n)):
        return "not all variables relevant"
    pts = np.array(list(itertools.product((1, -1), repeat=n)), dtype=np.int64)  # 2^n x n
    total = np.zeros(len(pts), dtype=np.int64)
    for S, c in terms.items():
        if not c:
            continue
        v = np.ones(len(pts), dtype=np.int64) * c
        for i in S:
            v = v * pts[:, i]
        total += v
    if not np.all(np.abs(total) == 4):
        return "f^2 != 1"
    return None

def flip_min(vec, n):
    """vec: list of (mask, c) sorted by mask.  Return lex-min over sign flips (variables + global) of the
    coefficient tuple.  Flip vector phi in GF(2)^(n+1); term mask S gets sign (-1)^{<phi, S|global>}."""
    basis = {}  # pivot bit -> (functional mask, target bit)
    out = []
    G = 1 << n
    for S, c in vec:
        f = S | G
        t = 0  # target value of functional under current constraints, and reduce
        m = f
        val = 0
        for b in range(n, -1, -1):
            if m >> b & 1 and b in basis:
                fm, fv = basis[b]
                m ^= fm
                val ^= fv
        if m == 0:
            # determined: sign = (-1)^val
            out.append(-c if val else c)
        else:
            # free: choose sign negative => want coefficient -|c|: need (-1)^{phi.f} c = -|c|
            want = 1 if c > 0 else 0   # phi.f = 1 flips sign
            # we need functional f to have value `want`; reduced form m has value val ^ (value of m)
            # value(m) = want ^ val
            pivot = m.bit_length() - 1
            basis[pivot] = (m, want ^ val)
            out.append(-abs(c))
    return tuple(out)

def invariants(terms, n):
    col = [0] * n
    mass = [0] * n
    prof = [[] for _ in range(n)]
    for S, c in terms.items():
        for i in S:
            mass[i] += c * c
            prof[i].append((len(S), abs(c)))
    col = [(mass[i], tuple(sorted(prof[i]))) for i in range(n)]
    for _ in range(n):
        new = []
        for i in range(n):
            nb = []
            for S, c in terms.items():
                if i in S:
                    nb.append((abs(c), tuple(sorted(col[j] for j in S if j != i))))
            new.append((col[i], tuple(sorted(nb))))
        # compress
        keys = sorted(set(new))
        new2 = [keys.index(x) for x in new]
        if len(set(new2)) == len(set(col)):
            col = new2
            break
        col = new2
    return col

def canon(terms, n):
    col = invariants(terms, n)
    classes = {}
    for i, c in enumerate(col):
        classes.setdefault(c, []).append(i)
    keys = sorted(classes)
    blocks = [classes[k] for k in keys]
    best = None
    items = list(terms.items())
    # permutations: new label order = concatenation of blocks, each block in any order
    for perm_parts in itertools.product(*[itertools.permutations(b) for b in blocks]):
        order = [v for part in perm_parts for v in part]   # order[new] = old
        relab = {old: new for new, old in enumerate(order)}
        vec = sorted(((sum(1 << relab[i] for i in S)), c) for S, c in items)
        cand = (tuple(m for m, _ in vec), flip_min(vec, n))
        if best is None or cand < best:
            best = cand
    return best

def xi3_terms():
    # variables: s=0,t=1, x_a..x_d = 2..5, y_a..y_d = 6..9
    # Xi_2(a,b,c,d) = (ac + bc + ad - bd)/2 ; Xi_3 = ((s+t)/2) Xi_2(x) + ((s-t)/2) Xi_2(y)
    def xi2(a, b, c, d):
        return {(a, c): 1, (b, c): 1, (a, d): 1, (b, d): -1}
    terms = {}
    for (u, sgn_t) in ((2, 1), (6, -1)):
        q = xi2(u, u + 1, u + 2, u + 3)
        for T, c in q.items():
            terms[tuple(sorted((0,) + T))] = c
            terms[tuple(sorted((1,) + T))] = c * sgn_t
    return terms

if __name__ == "__main__":
    n = int(sys.argv[1]); path = sys.argv[2]
    sols = parse(path)
    print("parsed %d solutions" % len(sols))
    bad = 0
    orbits = {}
    for t in sols:
        err = verify(t, n)
        if err:
            bad += 1
            print("INVALID:", err, t)
            continue
        cf = canon(t, n)
        orbits.setdefault(cf, []).append(t)
    print("invalid: %d ; valid: %d ; orbits under Sym(n) x negations x global sign: %d" % (bad, len(sols) - bad, len(orbits)))
    # report orbit representatives with mass profile
    for cf, reps in sorted(orbits.items(), key=lambda kv: kv[0]):
        t = reps[0]
        mass = [0] * n
        for S, c in t.items():
            for i in S:
                mass[i] += c * c
        sizes = sorted(len(S) for S in t)
        print("orbit: masses=%s  |S| multiset=%s  #labelled found=%d  rep=%s" % (
            sorted(mass), sizes, len(reps),
            " ".join("%s:%d" % (",".join(str(i + 1) for i in S), c) for S, c in sorted(t.items()))))
    if "--xi3" in sys.argv:
        x = xi3_terms()
        err = verify(x, 10)
        print("Xi_3 verification:", "OK" if err is None else err)
        cf = canon(x, 10)
        print("Xi_3 orbit found in search output:", cf in orbits)
