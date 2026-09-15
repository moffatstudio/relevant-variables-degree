# Independent check of Wellens (2019), Tables 1 and 2

Why this exists: the VibeMathed curator pointed out (2026-09-15) that Wellens, arXiv:1903.08214v2,
Table 2 bounds W(f) = sum_i 2^{-deg_i f} by 3.9375 at degree 8, hence R_8 <= 256 * 3.9375 = 1008 < 8 * 2^7.
So the Nisan–Szegedy bound was already known not to be attained for d >= 8 (d >= 9 follows from the
uniform bound 4.416 * 2^d). Before correcting the paper's novelty claim we re-derived those numbers.

`wellens_verify.py` (Python 3, numpy, scipy; exact `fractions` arithmetic for every certificate):

1. **Table 1** (LP upper bounds b(d) on block sensitivity, Wellens' Proposition 9). For each d <= 8 and
   every b up to 2 d^2 (so Tal's bs <= deg^2 is not relied on) and tau in {0,1}, the LP is solved in
   floating point and the verdict is then certified exactly: a rational feasible point, or a rational
   Farkas certificate of infeasibility. No uncertified verdict remains.
   Result: b(d) = 1, 3, 6, 10, 15, 21, 29, 38 — identical to Wellens' Table 1.
2. **Table 2** (Lemma 6 recursion W(b,d) <= min(d/2, max_{l,k} l d 2^{-d} + W(b-l, d-k)), exact rationals,
   computed both with the monotone convention and with Wellens' literal "W(b,d) = 0 for b > b(d)").
   Result: W <= d/2 for d = 1..7 (no improvement on Nisan–Szegedy) and W <= 63/16 = 3.9375 at d = 8,
   so R_8 <= 1008. Identical to Wellens' Table 2 for d <= 8.
3. **Margin.** Lemma 6 beats d/2 at degree d only if the block-sensitivity bound at that degree is at
   most 3, 5, 8, 14, 23, 39 for d = 3..8. The certified LP bounds are 6, 10, 15, 21, 29, 38, so the
   method fails for d <= 7 and succeeds at d = 8 with a margin of one.

The soundness of Lemma 6 itself (inequality (4) iterated over a maximal family of disjoint top-degree
monomials, Proposition 5 on block sensitivity) was read and checked by hand; it is not re-proved here.

Full output: `OUTPUT.txt`.
