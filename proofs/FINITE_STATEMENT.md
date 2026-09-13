# Finite reformulation of "R_3 <= 10" (for independent search and Lean certification)

Let n >= 1. A *coefficient vector* is an integer-valued map N : {S ⊆ [n] : |S| <= 3} -> Z (write n_S = N(S)). Define
   f_N(x) := (1/4) sum_S n_S chi_S(x),   chi_S(x) = prod_{i in S} x_i,   x in {-1,1}^n.

Statement F(n): there is NO coefficient vector N with
  (i)   sum_S n_S^2 = 16;
  (ii)  for every nonempty U ⊆ [n]:  sum over ordered pairs (S,T) with S Δ T = U of n_S n_T = 0;
  (iii) every i in [n] lies in some S with n_S ≠ 0.

Equivalently (i)+(ii) say f_N^2 ≡ 1 as a function on the cube (since chi_S chi_T = chi_{S Δ T} and (1/16) sum_{S,T} n_S n_T
chi_{S Δ T} = 1 iff the U = ∅ coefficient is 16 and all other coefficients vanish), i.e. f_N is {-1,1}-valued of degree <= 3;
(iii) says all n variables are relevant (a variable appears in the Fourier support iff f_N depends on it).

Claims to certify:  F(11) is TRUE (hence F(12) etc. — relevance of 12 variables would give an 11-variable... no: F(12)
follows separately; both are claimed).  F(10) is FALSE: the CHS function
   Xi_3 = ((s+t)/2) Xi_2(x) + ((s-t)/2) Xi_2(y),   Xi_2(a,b,c,d) = ((a+b)/2) c + ((a-b)/2) d,
has 10 relevant variables and degree 3 (its coefficients are ±1/4 on 16 triples ... check: Xi_2 = (ac + bc + ad - bd)/2,
so Xi_3 = (1/4)[ (s+t)(x_a x_c + x_b x_c + x_a x_d - x_b x_d) + (s-t)(y_a y_c + y_b y_c + y_a y_d - y_b y_d) ], 16 terms ±1/4).

Reduction (standard, to be cited or formalised separately): if f : {-1,1}^n -> {-1,1} has real multilinear degree <= 3
then every Fourier coefficient f^(S) is an integer multiple of 2^{1-3} = 1/4 (granularity), so N := 4 f^ is a coefficient
vector, f = f_N, and f^2 ≡ 1 gives (i),(ii); relevance of all variables gives (iii). Hence F(n) ⇒ no degree-3 Boolean
function has n relevant variables. Therefore F(11) ⇒ R_3 <= 10, and with Xi_3, R_3 = 10.

Elementary facts that any complete search may use (each provable in two lines from f_N^2 ≡ 1, no other input):
  E1. For each i, the derivative D_i f_N = (f_N(x^{i->1}) - f_N(x^{i->-1}))/2 = (1/4) sum_{S ∋ i} n_S chi_{S \ i} takes values
      in {-1,0,1}; hence 4 D_i f_N = sum_{S ∋ i} n_S chi_{S \ i} takes values in {0, ±4} at every x.
  E2. Parseval: sum_{S ∋ i} n_S^2 = 16 Pr[D_i f_N ≠ 0] is an integer in [4, 16] for relevant i (a nonzero degree-<=2 function is
      nonzero on >= 1/4 of the cube), and sum_i sum_{S ∋ i} n_S^2 = sum_S |S| n_S^2 <= 48.
  E3. Symmetries preserving (i)-(iii): permutations of [n]; negating variable i (n_S -> -n_S for S ∋ i); global sign N -> -N.
Anything beyond E1-E3 (e.g. the classification of link shapes in R3_equals_10.md) must NOT be assumed by an independent search;
it may be re-derived inside the search by brute force where it is a finite check.
