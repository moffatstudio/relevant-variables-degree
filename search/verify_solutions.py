#!/usr/bin/env python3
"""
Independent, from-scratch checker for search/sol2_n*.txt against FINITE_STATEMENT.md's F(n).

Parses "SOL S1:c1 S2:c2 ..." lines (subset S given as comma-separated 1-based indices, or
"e" for the empty set), builds f_N = (1/4) sum_S n_S chi_S by brute-force evaluation over
all 2^n points of {-1,1}^n, and checks:
  (i)   sum n_S^2 == 16
  (ii)  f_N(x) in {+1,-1} for every x  (equivalent to the pointwise |4 f_N(x)| == 4 check)
  (iii) every variable i in [n] is relevant: exists x,y differing only in coordinate i with
        f_N(x) != f_N(y) (equivalently i appears in some S with n_S != 0 AND flipping i
        actually changes some evaluation -- we check the direct relevance definition, not
        just "appears in some nonzero S", so this is a genuine independent check of (iii)).

Does not import or reuse any code from r3search.c / r3search2.c. Pure Python, O(2^n * |terms|).

Usage: python verify_solutions.py sol2_n6.txt sol2_n7.txt sol2_n8.txt sol2_n10.txt
"""
import sys
import re

def parse_line(line, n_hint=None):
    line = line.strip()
    if not line or not line.startswith("SOL"):
        return None
    parts = line.split()[1:]
    terms = []
    maxvar = 0
    for p in parts:
        subset_str, coef_str = p.rsplit(":", 1)
        coef = int(coef_str)
        if subset_str == "e":
            S = frozenset()
        else:
            idx = [int(t) for t in subset_str.split(",")]
            S = frozenset(idx)
            if idx:
                maxvar = max(maxvar, max(idx))
        terms.append((S, coef))
    return terms, maxvar

def evaluate_all(terms, n):
    """Return list f[x] for x in 0..2^n-1 (bit i-1 of x is variable i, 0->+1,1->-1),
    where f(x) = (1/4) sum_S n_S chi_S(x), chi_S(x) = prod_{i in S} sign(x,i)."""
    N = 1 << n
    f4 = [0] * N  # stores 4*f(x), should end up integer in {-4,...,4}
    # precompute chi_S(x) contributions termwise for speed: for each term, sign = (-1)^popcount(x & mask & S)
    for S, c in terms:
        mask = 0
        for i in S:
            mask |= 1 << (i - 1)
        for x in range(N):
            bits = bin(x & mask).count("1")
            sign = -1 if (bits & 1) else 1
            f4[x] += c * sign
    return f4

def check_solution(terms, n):
    errors = []
    # (i)
    sumsq = sum(c * c for _, c in terms)
    if sumsq != 16:
        errors.append(f"(i) failed: sum n_S^2 = {sumsq} != 16")

    f4 = evaluate_all(terms, n)
    N = 1 << n
    # (ii)
    bad = [x for x in range(N) if f4[x] not in (4, -4)]
    if bad:
        errors.append(f"(ii) failed: f_N not +-1 at {len(bad)} points, e.g. x={bad[0]} f4={f4[bad[0]]}")

    # (iii) genuine relevance: for each i in 1..n, exists x with f4[x] != f4[x XOR bit_i]
    for i in range(1, n + 1):
        bit = 1 << (i - 1)
        relevant = False
        for x in range(N):
            if x & bit:
                continue  # only check each pair once (x with bit unset, and x|bit)
            if f4[x] != f4[x | bit]:
                relevant = True
                break
        if not relevant:
            errors.append(f"(iii) failed: variable {i} is not relevant")

    return errors

def main():
    files = sys.argv[1:]
    if not files:
        print(__doc__)
        sys.exit(1)
    total_checked = 0
    total_failed = 0
    for fname in files:
        m = re.search(r"n(\d+)", fname)
        n_from_name = int(m.group(1)) if m else None
        with open(fname, "r", encoding="utf-8") as f:
            lines = [l for l in f if l.strip()]
        nsol = 0
        nfail = 0
        for lineno, line in enumerate(lines, 1):
            parsed = parse_line(line)
            if parsed is None:
                continue
            terms, maxvar = parsed
            n = n_from_name if n_from_name is not None else maxvar
            if maxvar > n:
                print(f"{fname}:{lineno}: WARNING max variable index {maxvar} > declared n={n}, using {maxvar}")
                n = maxvar
            nsol += 1
            errs = check_solution(terms, n)
            if errs:
                nfail += 1
                print(f"{fname}:{lineno}: FAIL: {'; '.join(errs)}")
                print(f"    line: {line.strip()}")
        print(f"{fname}: {nsol} solutions checked, {nfail} failed conditions (i)-(iii)")
        total_checked += nsol
        total_failed += nfail
    print(f"TOTAL: {total_checked} checked, {total_failed} failed")
    sys.exit(1 if total_failed else 0)

if __name__ == "__main__":
    main()
