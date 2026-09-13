"""Referee check for Step 4: f = (1/4) sum over the 16 faces of two vertex-disjoint octahedra of eps_S chi_S
is never {-1,1}-valued, for ALL 2^16 sign patterns. Also re-checks the value-set argument and reports the
range of values of the single-octahedron piece f_1 (must be non-constant for every sign pattern)."""
import itertools, numpy as np

# octahedron on vertices 0..5 with antipodal pairs (0,1),(2,3),(4,5): faces = one from each pair
oct_faces = [(a, b, c) for a in (0, 1) for b in (2, 3) for c in (4, 5)]
pts = np.array(list(itertools.product([-1, 1], repeat=6)))  # 64 x 6
M = np.stack([pts[:, a] * pts[:, b] * pts[:, c] for a, b, c in oct_faces], axis=1)  # 64 x 8
signs = np.array(list(itertools.product([-1, 1], repeat=8)))  # 256 x 8
vals = (M @ signs.T) / 4.0  # 64 x 256 : values of f_1 for each sign pattern
ranges = [frozenset(np.round(vals[:, k], 6)) for k in range(256)]
print("number of sign patterns for one octahedron:", len(ranges))
print("min |range(f_1)| over sign patterns:", min(len(r) for r in ranges), " (must be >= 2)")
print("distinct value-sets of f_1:", sorted({tuple(sorted(r)) for r in ranges}))
# direct check for all 65536 combined sign patterns: is f_1(x)+f_2(y) in {-1,1} for all x,y ?
bad = 0
for k1 in range(256):
    r1 = np.array(sorted(ranges[k1]))
    for k2 in range(256):
        r2 = np.array(sorted(ranges[k2]))
        s = (r1[:, None] + r2[None, :]).ravel()
        if np.all(np.isin(np.round(s, 6), [-1.0, 1.0])):
            bad += 1
print("combined sign patterns giving a Boolean f:", bad, " (must be 0)")
# also spot-check the fully direct evaluation on the 4096-point cube for a few random sign patterns
rng = np.random.default_rng(1)
pts12 = np.array(list(itertools.product([-1, 1], repeat=12)))
faces12 = oct_faces + [(a + 6, b + 6, c + 6) for a, b, c in oct_faces]
M12 = np.stack([pts12[:, a] * pts12[:, b] * pts12[:, c] for a, b, c in faces12], axis=1)
for _ in range(20):
    eps = rng.choice([-1, 1], size=16)
    f = M12 @ eps / 4.0
    assert not np.all(np.isin(f, [-1.0, 1.0]))
print("direct 4096-point evaluation for 20 random sign patterns: none Boolean. PASS")
