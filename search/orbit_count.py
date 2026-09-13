"""
Sum of orbit sizes of the solutions found by the search, for comparison with the labelled brute-force count
(brute_small_n.py for n<=4, brute56.c for n=5,6).

For each orbit representative t (under G = Sym(n) x variable negations x global sign, |G| = n! 2^(n+1))
we compute |Aut(t)| directly: for every permutation pi, relabel t; the relabelled support must equal the
support; then the sign pattern must satisfy a GF(2) linear system (one equation per term), whose number of
solutions is 2^(n+1-rank) if consistent.  |orbit| = |G| / |Aut|.
Usage: python orbit_count.py n solutions.txt
"""
import sys, itertools, math
from check_solutions import parse, verify, canon

def aut_size(terms, n):
    items = {frozenset(S): c for S, c in terms.items()}
    total = 0
    G = 1 << n
    for perm in itertools.permutations(range(n)):
        rel = {}
        ok = True
        for S, c in items.items():
            T = frozenset(perm[i] for i in S)
            if T not in items or abs(items[T]) != abs(c):
                ok = False
                break
            rel[T] = c  # coefficient of image at T (before signs)
        if not ok:
            continue
        # need phi in GF(2)^(n+1): (-1)^{<phi, T|G>} * rel[T] == items[T]
        rows = []
        for T, c in rel.items():
            f = sum(1 << i for i in T) | G
            b = 0 if c == items[T] else 1
            rows.append((f, b))
        # gaussian elimination
        basis = {}
        consistent = True
        for f, b in rows:
            for bit in range(n, -1, -1):
                if f >> bit & 1 and bit in basis:
                    bf, bb = basis[bit]
                    f ^= bf; b ^= bb
            if f == 0:
                if b:
                    consistent = False
                    break
            else:
                basis[f.bit_length() - 1] = (f, b)
        if consistent:
            total += 1 << (n + 1 - len(basis))
    return total

if __name__ == "__main__":
    n = int(sys.argv[1]); path = sys.argv[2]
    sols = parse(path)
    orbits = {}
    bad = 0
    for t in sols:
        if verify(t, n):
            bad += 1
            continue
        orbits.setdefault(canon(t, n), t)
    Gsize = math.factorial(n) * (1 << (n + 1))
    total = 0
    for cf, t in orbits.items():
        a = aut_size(t, n)
        assert Gsize % a == 0
        total += Gsize // a
    print("n=%d: %d solutions parsed, %d invalid, %d orbits, sum of orbit sizes (labelled count) = %d" % (n, len(sols), bad, len(orbits), total))
