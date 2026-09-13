"""Brute-force check of Lemma A (NS_never_tight.md).

q = 2^{-m} sum_j n_j chi_{T_j}, distinct T_j, nonzero integers n_j, sum n_j^2 = N = 2^m,
q {-1,0,1}-valued and not identically 0.
Claim: all n_j = +-1, J = N, {T_j} is an affine m-dim subspace of F_2^g, and
n_j n_k n_l n_r = +1 whenever T_j ^ T_k ^ T_l ^ T_r = 0.

We enumerate every coefficient multiset (positive parts, sum of squares = N), every
assignment to distinct subsets of a ground set of size g, every sign pattern, and test.
m = 2 on g = 3,4 ; m = 3 on g = 4 (exhaustive), and g = 5 with WLOG T_1 = empty set and
n_1 > 0 (translation by chi_{T_1} and global negation preserve everything).
"""
import itertools, sys, time
import numpy as np

def char_table(g):
    pts = np.array(list(itertools.product([1, -1], repeat=g)), dtype=np.int8)  # 2^g x g
    subsets = np.arange(2 ** g)
    # chi_T(x) = prod_{i in T} x_i
    tab = np.ones((2 ** g, 2 ** g), dtype=np.int8)  # rows: subsets, cols: points
    for T in range(2 ** g):
        mask = [(T >> i) & 1 for i in range(g)]
        v = np.ones(2 ** g, dtype=np.int8)
        for i, b in enumerate(mask):
            if b:
                v = v * pts[:, i]
        tab[T] = v
    return tab

def sq_partitions(N, maxpart=None):
    """multisets of positive integers with sum of squares N (nonincreasing)."""
    if maxpart is None:
        maxpart = int(N ** 0.5)
    if N == 0:
        yield ()
        return
    for a in range(min(maxpart, int(N ** 0.5)), 0, -1):
        for rest in sq_partitions(N - a * a, a):
            yield (a,) + rest

def is_affine(sets):
    S = set(sets)
    for a in S:
        for b in S:
            for c in S:
                if (a ^ b ^ c) not in S:
                    return False
    return True

def sign_condition(sets, coeffs):
    idx = {T: i for i, T in enumerate(sets)}
    for a in sets:
        for b in sets:
            for c in sets:
                d = a ^ b ^ c
                if d in idx:
                    if coeffs[idx[a]] * coeffs[idx[b]] * coeffs[idx[c]] * coeffs[idx[d]] != 1:
                        return False
    return True

def run(m, g, wlog=False):
    N = 2 ** m
    tab = char_table(g)
    nsub = 2 ** g
    valid = 0
    bad = []
    tested = 0
    t0 = time.time()
    for parts in sq_partitions(N):
        J = len(parts)
        if J > nsub:
            continue
        mags = np.array(parts, dtype=np.int64)
        # distinct orderings of magnitudes over J labelled slots
        perms = sorted(set(itertools.permutations(parts)))
        signs_all = np.array(list(itertools.product([1, -1], repeat=J)), dtype=np.int64)
        if wlog:
            signs_all = signs_all[signs_all[:, 0] == 1]
        if wlog:
            others = range(1, nsub)
            combos = ((0,) + c for c in itertools.combinations(others, J - 1))
        else:
            combos = itertools.combinations(range(nsub), J)
        for sets in combos:
            rows = tab[list(sets)].astype(np.int64)  # J x 2^g
            for perm in perms:
                mag = np.array(perm, dtype=np.int64)
                coefs = signs_all * mag  # (#signs) x J
                s = coefs @ rows  # (#signs) x 2^g
                tested += s.shape[0]
                ok = np.all((s == 0) | (s == N) | (s == -N), axis=1) & np.any(s != 0, axis=1)
                for si in np.nonzero(ok)[0]:
                    c = coefs[si]
                    valid += 1
                    cond = (np.all(np.abs(c) == 1) and len(sets) == N and is_affine(sets)
                            and sign_condition(sets, [int(x) for x in c]))
                    if not cond:
                        bad.append((sets, tuple(int(x) for x in c)))
    print(f"m={m} g={g} wlog={wlog}: tested {tested} instances, {valid} valid q's, "
          f"{len(bad)} violating Lemma A, {time.time()-t0:.1f}s")
    for b in bad[:10]:
        print("  VIOLATION", b)
    return len(bad) == 0

if __name__ == "__main__":
    allok = True
    allok &= run(2, 3)
    allok &= run(2, 4)
    allok &= run(3, 4)
    allok &= run(3, 5, wlog=True)
    print("LEMMA A CHECK:", "PASS" if allok else "FAIL")
