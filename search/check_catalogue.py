"""
Independent brute-force cross-check of the link catalogue produced by r3search -links K M.

A "link" is an integer polynomial g = sum_T c_T chi_T over sets T of size <= 2 on variables {1..K},
with 4 <= sum c_T^2 <= M and g(x) in {0,+-4} for all x in {-1,1}^K.
This script enumerates ALL such polynomials naively (no pruning except the mass budget), reduces them
to canonical forms under Sym(K) x (variable negations) x (global sign), and compares the set of orbits
with the catalogue file (each catalogue line reduced to canonical form the same way).

Usage: python check_catalogue.py K M catalogue.txt
"""
import sys, itertools

def terms_of(K):
    ts = [()]
    ts += [(i,) for i in range(1, K + 1)]
    ts += [(i, j) for i in range(1, K + 1) for j in range(i + 1, K + 1)]
    return ts

def values(poly, K):
    # poly: dict term->coef ; returns tuple of values over all 2^K points
    out = []
    for x in itertools.product((1, -1), repeat=K):
        s = 0
        for T, c in poly.items():
            p = c
            for i in T:
                p *= x[i - 1]
            s += p
        out.append(s)
    return out

def canon(poly, K):
    """canonical form: min over all relabellings (Sym(K)), variable negations, global sign of the sorted term list."""
    items = [(T, c) for T, c in poly.items() if c]
    best = None
    for perm in itertools.permutations(range(1, K + 1)):
        relab = {i + 1: perm[i] for i in range(K)}
        base = [(tuple(sorted(relab[i] for i in T)), c) for T, c in items]
        for flips in range(1 << K):
            for gl in (1, -1):
                cur = []
                for T, c in base:
                    s = gl
                    for i in T:
                        if flips >> (i - 1) & 1:
                            s = -s
                    cur.append((T, c * s))
                cur.sort()
                cur = tuple(cur)
                if best is None or cur < best:
                    best = cur
    return best

def brute(K, M):
    ts = terms_of(K)
    found = []
    poly = {}
    def rec(idx, mass):
        if idx == len(ts):
            if mass >= 4:
                vals = values(poly, K)
                if all(v in (0, 4, -4) for v in vals):
                    found.append(dict(poly))
            return
        T = ts[idx]
        for c in range(-4, 5):
            if mass + c * c > M:
                continue
            if c:
                poly[T] = c
            else:
                poly.pop(T, None)
            rec(idx + 1, mass + c * c)
        poly.pop(T, None)
    rec(0, 0)
    return found

def parse_catalogue(path):
    out = []
    for line in open(path):
        if not line.startswith("LINK"):
            continue
        parts = line.split()
        poly = {}
        for tok in parts[3:]:
            T, c = tok.split(":")
            T = () if T == "e" else tuple(int(a) for a in T.split(","))
            poly[T] = int(c)
        m = int(parts[1][2:]); k = int(parts[2][2:])
        out.append((m, k, poly))
    return out

if __name__ == "__main__":
    K, M, path = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    found = brute(K, M)
    print("brute force: %d labelled valid links on <= %d variables with mass in [4,%d]" % (len(found), K, M))
    # validate every one uses only variables 1..K (trivial) ; reduce to orbits
    orbits = {}
    for p in found:
        used = sorted({i for T in p for i in T})
        cf = canon(p, K)
        orbits.setdefault(cf, 0)
        orbits[cf] += 1
    print("brute force: %d orbits" % len(orbits))
    cat = parse_catalogue(path)
    # keep only catalogue entries with k <= K and m <= M ; verify each is valid
    catorbits = set()
    bad = 0
    for m, k, poly in cat:
        if k > K or m > M:
            continue
        vals = values(poly, K)
        if not all(v in (0, 4, -4) for v in vals) or sum(c * c for c in poly.values()) != m:
            bad += 1
        catorbits.add(canon(poly, K))
    print("catalogue: %d entries with k<=%d, m<=%d; %d invalid" % (len(catorbits), K, M, bad))
    missing = set(orbits) - catorbits
    extra = catorbits - set(orbits)
    print("orbits missing from catalogue: %d ; extra in catalogue: %d" % (len(missing), len(extra)))
    for o in list(missing)[:10]:
        print("  MISSING", o)
    for o in list(extra)[:10]:
        print("  EXTRA", o)
    print("MATCH" if not missing and not extra and not bad else "MISMATCH")
