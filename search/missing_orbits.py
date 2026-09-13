"""List orbits present in brute force (n<=4) but absent from a search output file."""
import sys, itertools
from check_solutions import canon, parse

def brute_orbits(n):
    pts = list(itertools.product((1, -1), repeat=n)); N = len(pts)
    subsets = [S for r in range(n + 1) for S in itertools.combinations(range(n), r)]
    chi = {S: [eval("*".join(["1"] + ["x[%d]" % i for i in S])) for x in pts] for S in subsets}
    orbits = {}
    for bits in range(1 << N):
        f = [1 if bits >> k & 1 else -1 for k in range(N)]
        coef = {}; ok = True
        for S in subsets:
            s = sum(f[k] * chi[S][k] for k in range(N))
            if len(S) > 3:
                if s: ok = False; break
                continue
            if (4 * s) % N: ok = False; break
            c = 4 * s // N
            if c: coef[S] = c
        if not ok: continue
        if set(i for S in coef for i in S) != set(range(n)): continue
        orbits.setdefault(canon(coef, n), coef)
    return orbits

n = int(sys.argv[1]); path = sys.argv[2]
b = brute_orbits(n)
found = set(canon(t, n) for t in parse(path))
print("brute orbits", len(b), "found", len(found), "missing", len(set(b) - found))
for cf, rep in b.items():
    if cf not in found:
        mass = [0]*n
        for S, c in rep.items():
            for i in S: mass[i] += c*c
        print("MISSING masses=%s rep=%s" % (mass, " ".join("%s:%d" % (",".join(str(i+1) for i in S), c) for S, c in sorted(rep.items()))))
