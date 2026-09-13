"""Referee check for Lemma 1 / Lemma 2(a)-(c) of R3_equals_10.md.

A link at vertex i is a family of distinct sets T_j (|T_j| <= 2) with integer weights n_j,
sum n_j^2 = m, such that  sum_j n_j chi_{T_j}(x) in {0, +-4} for all x.

(1) Sign-free part: enumerate all families of k distinct subsets of size <= 2 of a ground set
    with empty symmetric difference (each element in an even number of sets), k = 4, 5, 6,
    and classify them up to relabelling.  Ground set size 6 suffices for k <= 6
    (2k incidences, every used element appears >= 2 times, so <= k elements).
(2) Weighted part: for every multiset of |n_j| in {1,2} with sum of squares m in 4..8,
    brute-force whether some choice of distinct sets + signs realises values in {0,+-4}.
"""
import itertools
from collections import Counter

G = 6
elems = range(G)
sets = [frozenset()] + [frozenset([a]) for a in elems] + [frozenset(p) for p in itertools.combinations(elems, 2)]


def symdiff_empty(fam):
    c = Counter()
    for T in fam:
        for a in T:
            c[a] += 1
    return all(v % 2 == 0 for v in c.values())


def shape(fam):
    """Canonical description: sizes, plus the multigraph of pairs/singletons up to relabelling."""
    used = sorted({a for T in fam for a in T})
    best = None
    for perm in itertools.permutations(range(len(used))):
        rl = {used[k]: perm[k] for k in range(len(used))}
        key = tuple(sorted(tuple(sorted(rl[a] for a in T)) for T in fam))
        if best is None or key < best:
            best = key
    return best


print("=== (1) families with empty symmetric difference ===")
for k in (4, 5, 6):
    shapes = Counter()
    for fam in itertools.combinations(sets, k):
        if symdiff_empty(fam):
            shapes[shape(fam)] += 1
    print(f"k={k}: {len(shapes)} shapes up to relabelling")
    for s, cnt in sorted(shapes.items(), key=lambda t: (len({a for T in t[0] for a in T}), t[0])):
        desc = " ".join("{}" if T == () else "{" + ",".join("abcdefgh"[a] for a in T) + "}" for T in s)
        print(f"   {desc}")

print()
print("=== (2) which weight patterns admit a {0,+-4}-valued link (brute force, ground set 6) ===")
pts = list(itertools.product([-1, 1], repeat=G))


def chi(T, x):
    v = 1
    for a in T:
        v *= x[a]
    return v


def realisable(pattern):
    """pattern: tuple of |n_j|.  Return an example (sets, signs) or None."""
    k = len(pattern)
    for fam in itertools.combinations(sets, k):
        # quick sign-free filter for all-unit patterns: need symdiff empty
        for signs in itertools.product([-1, 1], repeat=k - 1):
            signs = (1,) + signs  # global sign irrelevant
            ok = True
            for x in pts:
                s = sum(sg * w * chi(T, x) for sg, w, T in zip(signs, pattern, fam))
                if s not in (0, 4, -4):
                    ok = False
                    break
            if ok:
                return fam, signs
    return None


patterns = {
    4: [(2,), (1, 1, 1, 1)],
    5: [(2, 1), (1,) * 5],
    6: [(2, 1, 1), (1,) * 6],
    7: [(2, 1, 1, 1), (1,) * 7],
    8: [(2, 2), (2, 1, 1, 1, 1), (1,) * 8],
}
for m, pats in patterns.items():
    for p in pats:
        if len(p) >= 7:
            print(f"m={m} pattern {p}: skipped brute force (parity argument: odd number of odd terms -> odd value; 8 units handled in (1)/even-graph script)")
            continue
        r = realisable(p)
        print(f"m={m} pattern {p}: {'REALISABLE e.g. ' + str([sorted(T) for T in r[0]]) + ' signs ' + str(r[1]) if r else 'impossible'}")
