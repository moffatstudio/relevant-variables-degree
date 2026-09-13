import Mathlib
/-!
# Finite statement F(n)  (FROZEN — do not edit)

Subsets of [n] = {0,…,n-1} are encoded as bitmasks `S : ℕ` with `S < 2^n`;
`i ∈ S` iff `S.testBit i`; symmetric difference is `S ^^^ T` (xor);
`card n S` is |S|.  A coefficient vector is `N : ℕ → ℤ`, vanishing on
subsets of size > 3 (values of `N` outside `S < 2^n` are never used).

F(n): there is no coefficient vector with
 (i)   ∑_S n_S² = 16,
 (ii)  for every nonempty U ⊆ [n]: ∑ over ordered pairs (S,T) with S Δ T = U of n_S n_T = 0,
 (iii) every i ∈ [n] lies in some S with n_S ≠ 0.
-/
namespace R3
open Finset

/-- number of elements of the subset of [n] encoded by the bitmask `S` -/
def card (n S : ℕ) : ℕ := ((range n).filter fun i => S.testBit i).card

/-- `N` is supported on subsets of size ≤ 3 -/
def IsCoeffVec (n : ℕ) (N : ℕ → ℤ) : Prop :=
  ∀ S, S < 2 ^ n → 3 < card n S → N S = 0

/-- (i)  ∑_S n_S² = 16 -/
def CondI (n : ℕ) (N : ℕ → ℤ) : Prop :=
  ∑ S ∈ range (2 ^ n), (N S) ^ 2 = 16

/-- (ii) for every nonempty U ⊆ [n], ∑_{(S,T) : S Δ T = U} n_S n_T = 0 -/
def CondII (n : ℕ) (N : ℕ → ℤ) : Prop :=
  ∀ U, 0 < U → U < 2 ^ n →
    ∑ S ∈ range (2 ^ n), ∑ T ∈ range (2 ^ n), (if S ^^^ T = U then N S * N T else 0) = 0

/-- (iii) every variable is relevant -/
def CondIII (n : ℕ) (N : ℕ → ℤ) : Prop :=
  ∀ i, i < n → ∃ S, S < 2 ^ n ∧ S.testBit i ∧ N S ≠ 0

/-- a solution of the finite problem on n variables -/
def IsSol (n : ℕ) (N : ℕ → ℤ) : Prop :=
  IsCoeffVec n N ∧ CondI n N ∧ CondII n N ∧ CondIII n N

/-- The finite statement F(n). -/
def F (n : ℕ) : Prop := ¬ ∃ N : ℕ → ℤ, IsSol n N

end R3
