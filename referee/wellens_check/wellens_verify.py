"""Independent exact re-verification of Wellens arXiv:1903.08214v2, Tables 1 and 2 (d <= 8).

Table 1: b(d) = largest b for which the LP of Proposition 9 is feasible (upper bound on bs for degree d).
  Every LP verdict is certified in exact rational arithmetic:
    feasible   -> an exact rational point satisfying every constraint,
    infeasible -> an exact Farkas certificate (y free, z >= 0, E^T y + G^T z = 0, e.y + h.z = -1).
  b is scanned up to 2 d^2 (Nisan-Szegedy's bs <= 2 deg^2), so Tal's bs <= deg^2 is not relied on.
Table 2: the Lemma 6 recursion W(b,d) <= min(d/2, max_{l,k} l d 2^-d + W(b-l, d-k)), exact Fractions.
"""
import math
from fractions import Fraction as F

import numpy as np
from scipy.optimize import linprog

DMAX = 8
TOL = 1e-7


def nodes_for(d, b):
    hi = max(b, d)
    raw = [(1 + hi) / 2 - (hi - 1) / 2 * math.cos(math.pi * (2 * i + 1) / (2 * d)) for i in range(d)]
    out = []
    for r in raw:
        c = min(max(int(round(r)), 1), hi)
        if c not in out:
            out.append(c)
    k = 1
    while len(out) < d:
        if k not in out:
            out.append(k)
        k += 1
    return sorted(out)


def lag_row(nodes, k):
    xs = [0] + nodes
    row = []
    for j in range(1, len(xs)):
        v = F(1)
        for m in range(len(xs)):
            if m != j:
                v *= F(k - xs[m], xs[j] - xs[m])
        row.append(v)
    return row


def build(d, b, tau):
    nodes = nodes_for(d, b)
    E = [lag_row(nodes, 1), lag_row(nodes, b)]
    e = [F(1), F(tau)]
    G, h = [], []
    for k in range(2, b):
        r = lag_row(nodes, k)
        G.append(r); h.append(F(1))
        G.append([-x for x in r]); h.append(F(0))
    return E, e, G, h


def solve_exact(A, c, n, default):
    """Solve A x = c (Fractions). Free columns take default values. None if inconsistent."""
    M = [list(A[i]) + [c[i]] for i in range(len(A))]
    piv_cols, r = [], 0
    for col in range(n):
        p = next((i for i in range(r, len(M)) if M[i][col] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        pv = M[r][col]
        M[r] = [x / pv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][col] != 0:
                f = M[i][col]
                M[i] = [a - f * bb for a, bb in zip(M[i], M[r])]
        piv_cols.append(col)
        r += 1
    for i in range(r, len(M)):
        if M[i][n] != 0:
            return None
    x = list(default)
    for i, col in enumerate(piv_cols):
        s = M[i][n]
        for j in range(n):
            if j != col and j not in piv_cols:
                s -= M[i][j] * x[j]
        x[col] = s
    return x


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def check_primal(E, e, G, h, x):
    return all(dot(E[i], x) == e[i] for i in range(len(E))) and all(dot(G[i], x) <= h[i] for i in range(len(G)))


def certify_feasible(E, e, G, h, xf):
    d = len(E[0])
    rnd = [F(float(v)).limit_denominator(10 ** 12) for v in xf]
    if G:
        Gf = np.array([[float(v) for v in row] for row in G])
        slack = np.array([float(v) for v in h]) - Gf @ xf
        act = [i for i in range(len(G)) if abs(slack[i]) < TOL]
    else:
        act = []
    x = solve_exact(E + [G[i] for i in act], e + [h[i] for i in act], d, rnd)
    if x is not None and check_primal(E, e, G, h, x):
        return True
    # fallback: maximise a uniform margin, round, repair the two equalities exactly
    if G:
        Gf = np.array([[float(v) for v in row] for row in G])
        Ef = np.array([[float(v) for v in row] for row in E])
        A_ub = np.hstack([Gf, np.ones((len(G), 1))])
        A_eq = np.hstack([Ef, np.zeros((2, 1))])
        c = np.zeros(d + 1); c[-1] = -1
        res = linprog(c, A_ub=A_ub, b_ub=[float(v) for v in h], A_eq=A_eq, b_eq=[float(v) for v in e],
                      bounds=[(None, None)] * d + [(None, 1)], method="highs")
        if res.status == 0:
            rnd = [F(float(v)).limit_denominator(10 ** 15) for v in res.x[:d]]
            x = solve_exact(E, e, d, rnd)
            if x is not None and check_primal(E, e, G, h, x):
                return True
    return False


def certify_infeasible(E, e, G, h):
    d = len(E[0])
    nv = 2 + len(G)
    cols = [[E[0][j], E[1][j]] + [G[i][j] for i in range(len(G))] for j in range(d)]
    A = cols + [e + h]
    c = [F(0)] * d + [F(-1)]
    Af = np.array([[float(v) for v in row] for row in A])
    obj = np.array([0.0, 0.0] + [1.0] * len(G))
    res = linprog(obj, A_eq=Af, b_eq=[float(v) for v in c],
                  bounds=[(None, None)] * 2 + [(0, None)] * len(G), method="highs-ds")
    if res.status != 0:
        return False
    support = [i for i in range(nv) if abs(res.x[i]) > 1e-12]
    A_s = [[row[i] for i in support] for row in A]
    rnd = [F(float(res.x[i])).limit_denominator(10 ** 12) for i in support]
    xs = solve_exact(A_s, c, len(support), rnd)
    if xs is None:
        return False
    full = [F(0)] * nv
    for i, v in zip(support, xs):
        full[i] = v
    if any(full[i] < 0 for i in range(2, nv)):
        return False
    return all(dot(A[r], full) == c[r] for r in range(len(A)))


def table1():
    bt = {0: 0}
    for d in range(1, DMAX + 1):
        best, bad = 1, []
        for b in range(2, 2 * d * d + 1):
            feas_any = False
            for tau in (0, 1):
                E, e, G, h = build(d, b, tau)
                Ef = [[float(v) for v in r] for r in E]
                Gf = [[float(v) for v in r] for r in G] if G else None
                res = linprog(np.zeros(d), A_ub=Gf, b_ub=[float(v) for v in h] if G else None,
                              A_eq=Ef, b_eq=[float(v) for v in e], bounds=[(None, None)] * d, method="highs-ds")
                if res.status == 0:
                    ok = certify_feasible(E, e, G, h, res.x)
                    if not ok and certify_infeasible(E, e, G, h):
                        ok, feasible = True, False
                    else:
                        feasible = True
                else:
                    ok = certify_infeasible(E, e, G, h)
                    feasible = False
                    if not ok and certify_feasible(E, e, G, h, np.zeros(d)):
                        ok, feasible = True, True
                if not ok:
                    bad.append((b, tau, "float says " + ("feasible" if res.status == 0 else "infeasible")))
                feas_any |= feasible
            if feas_any:
                best = b
        bt[d] = best
        print(f"d={d}: b(d)={best}  (scanned b<= {2*d*d}; uncertified: {bad if bad else 'none'})", flush=True)
    return bt


def table2(bt, cap_mode="clamp"):
    memo = {}

    def U(b, d):
        if d <= 0 or b <= 0:
            return F(0)
        if b > bt[d]:
            if cap_mode == "clamp":
                b = bt[d]
            else:  # Wellens' literal convention W(b,d)=0 for b > b(d)
                return F(0)
        key = (b, d)
        if key in memo:
            return memo[key]
        best = F(0)
        for l in range(1, b + 1):
            for k in range(1, d + 1):
                best = max(best, F(l * d, 2 ** d) + U(b - l, d - k))
        memo[key] = min(F(d, 2), best)
        return memo[key]

    return {d: U(bt[d], d) for d in range(1, DMAX + 1)}, U


if __name__ == "__main__":
    print("== Table 1 (exact-certified LP bounds on bs) ==")
    bt = table1()
    print("Wellens Table 1:", [1, 3, 6, 10, 15, 21, 29, 38])
    print("recomputed     :", [bt[d] for d in range(1, DMAX + 1)])
    print("\n== Table 2 (Lemma 6 recursion, exact) ==")
    t2, U = table2(bt)
    t2w, _ = table2(bt, cap_mode="zero")
    for d in range(1, DMAX + 1):
        ns = d * 2 ** (d - 1)
        print(f"d={d}: W<= {t2[d]} = {float(t2[d]):.4f} (Wellens-convention {float(t2w[d]):.4f})  "
              f"R_d <= {t2[d] * 2**d}  vs NS {ns}  beats NS: {t2[d] * 2**d < ns}")
    print("\n== How small would bs(d) need to be for Lemma 6 to beat d/2 at degree d? ==")
    for d in range(3, DMAX + 1):
        bt_top = dict(bt)
        bt_top[d] = d * d  # do not clamp the top degree at its LP bound; lower degrees keep certified b(d')
        _, U_top = table2(bt_top)
        thr = max((b for b in range(1, d * d + 1) if U_top(b, d) < F(d, 2)), default=None)
        print(f"d={d}: Lemma 6 beats NS iff bs-bound at degree {d} is <= {thr} (certified LP bound {bt[d]})")
