"""
Ground truth for tiny n: enumerate ALL Boolean functions f:{-1,1}^n -> {-1,1} (2^(2^n) of them, n<=4),
keep those with Fourier degree <= 3 and all n variables relevant, and count orbits under
Sym(n) x negations x global sign using the same canonical form as check_solutions.py.
Compare with `python check_solutions.py n sol_n<n>.txt`.
Usage: python brute_small_n.py n
"""
import sys, itertools
from fractions import Fraction
from check_solutions import canon

def main(n):
    pts = list(itertools.product((1, -1), repeat=n))
    N = len(pts)
    subsets = [S for r in range(n + 1) for S in itertools.combinations(range(n), r)]
    chi = {S: [ (lambda x: (lambda p: p)(eval("*".join(["1"] + ["x[%d]" % i for i in S])) ) )(x) for x in pts] for S in subsets}
    count = 0
    orbits = set()
    for bits in range(1 << N):
        f = [1 if bits >> k & 1 else -1 for k in range(N)]
        coef = {}
        ok = True
        for S in subsets:
            s = sum(f[k] * chi[S][k] for k in range(N))
            # n_S = 4 * fhat(S) = 4 * s / N
            if len(S) > 3:
                if s != 0:
                    ok = False
                    break
                continue
            if (4 * s) % N != 0:
                ok = False
                break
            c = 4 * s // N
            if c:
                coef[S] = c
        if not ok:
            continue
        rel = set(i for S in coef for i in S)
        if rel != set(range(n)):
            continue
        assert sum(c * c for c in coef.values()) == 16
        count += 1
        orbits.add(canon(coef, n))
    print("n=%d: %d labelled degree-<=3 Boolean functions with all %d variables relevant; %d orbits" % (n, count, n, len(orbits)))

if __name__ == "__main__":
    main(int(sys.argv[1]))
