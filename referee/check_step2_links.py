"""Referee check for Step 2: a {-1,0,1}-valued function q = (1/4) sum_{j=1}^4 eps_j chi_{T_j}
(four DISTINCT pairs T_j) must have T_1 D T_2 D T_3 D T_4 = empty, prod eps = +1, and the pairs must form a 4-cycle.
Brute force over all 4-sets of distinct pairs on m=8 vertices (enough: 4 pairs touch <= 8 vertices) and all signs."""
import itertools, numpy as np

m = 8
pts = np.array(list(itertools.product([-1, 1], repeat=m)))  # 256 x 8
pairs = list(itertools.combinations(range(m), 2))
chi = {p: pts[:, p[0]] * pts[:, p[1]] for p in pairs}

def is_c4(T):
    deg = {}
    for a, b in T:
        deg[a] = deg.get(a, 0) + 1
        deg[b] = deg.get(b, 0) + 1
    if len(deg) != 4 or any(d != 2 for d in deg.values()):
        return False
    # connected 2-regular on 4 vertices with 4 distinct edges -> C4
    adj = {v: set() for v in deg}
    for a, b in T:
        adj[a].add(b); adj[b].add(a)
    seen = {T[0][0]}; stack = [T[0][0]]
    while stack:
        v = stack.pop()
        for w in adj[v]:
            if w not in seen:
                seen.add(w); stack.append(w)
    return len(seen) == 4

n_good = n_bad_shape = n_bad_sign = 0
shape_ok_sign_ok_but_not_valued = 0
for T in itertools.combinations(pairs, 4):
    symdiff = set()
    for p in T:
        symdiff ^= set(p)
    c4 = is_c4(T)
    assert c4 == (len(symdiff) == 0), (T, symdiff, c4)  # sym-diff empty  <=>  4-cycle
    cols = np.stack([chi[p] for p in T], axis=1)
    for eps in itertools.product([-1, 1], repeat=4):
        vals = cols @ np.array(eps)  # in {-4,-2,0,2,4}
        valued = bool(np.all(np.isin(vals, [-4, 0, 4])))
        pred = c4 and (np.prod(eps) == 1)
        if valued != pred:
            print("MISMATCH", T, eps, valued, pred)
        if valued:
            n_good += 1
        elif not c4:
            n_bad_shape += 1
        else:
            n_bad_sign += 1
print("4-sets of distinct pairs:", len(list(itertools.combinations(pairs, 4))))
print("valued (all such are C4 with even sign product):", n_good)
print("not valued because shape is not C4:", n_bad_shape)
print("not valued because C4 but odd sign product:", n_bad_sign)
print("Step 2 check: {-1,0,1}-valued  <=>  (pairs form C4 and prod eps = +1). PASS if no MISMATCH lines above.")
