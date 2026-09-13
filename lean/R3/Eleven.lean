import R3.Statement
import R3.Basic
import R3.Mass
import R3.Octahedron
import R3.DeltaFour
import R3.DeltaTwo
import R3.DeltaZero

/-!
# `F 11` — assembly of the three mass cases

`bookkeeping` at `n = 11` reads

  δ + e = 4,   δ := ∑_v (mass v − 4),   e := ∑_S (3 − |S|) n_S².

Both summands are termwise nonnegative (`four_le_mass`; `IsCoeffVec`), so δ ≤ 4 and
e ≤ 4.  Every mass is 4, 6 or 8 (`mass_cases`), so the possible mass profiles at
`n = 11` are:

* all masses 4      (δ = 0)          — `eleven_delta_four`
* one mass 6, rest 4 (δ = 2)         — `eleven_delta_two`
* one mass 8, or two masses 6 (δ = 4) ⇒ e = 0 ⇒ `Cubic 11 N` — `eleven_delta_zero`

Each case is already `False`, hence `F 11`.
-/

namespace R3
open Finset

/-- the excess `∑_S (3 − |S|) n_S²` is nonnegative: `N` is supported in size ≤ 3 -/
lemma excess_nonneg {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) :
    0 ≤ ∑ S ∈ range (2 ^ n), ((3 : ℤ) - card n S) * (N S) ^ 2 := by
  apply sum_nonneg
  intro S hS
  rcases eq_or_ne (N S) 0 with h | h
  · simp [h]
  · have hc : card n S ≤ 3 := by
      by_contra hcc
      exact h (hsol.1 S (mem_range.mp hS) (by omega))
    have hc' : ((card n S : ℕ) : ℤ) ≤ 3 := by exact_mod_cast hc
    have := sq_nonneg (N S)
    nlinarith

/-- if the excess vanishes then every supported set has size exactly 3 -/
lemma cubic_of_excess_le_zero {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N)
    (h : ∑ S ∈ range (2 ^ n), ((3 : ℤ) - card n S) * (N S) ^ 2 ≤ 0) : Cubic n N := by
  have hnn : ∀ S ∈ range (2 ^ n), 0 ≤ ((3 : ℤ) - card n S) * (N S) ^ 2 := by
    intro S hS
    rcases eq_or_ne (N S) 0 with h0 | h0
    · simp [h0]
    · have hc : card n S ≤ 3 := by
        by_contra hcc
        exact h0 (hsol.1 S (mem_range.mp hS) (by omega))
      have hc' : ((card n S : ℕ) : ℤ) ≤ 3 := by exact_mod_cast hc
      have := sq_nonneg (N S)
      nlinarith
  have hz : ∑ S ∈ range (2 ^ n), ((3 : ℤ) - card n S) * (N S) ^ 2 = 0 :=
    le_antisymm h (sum_nonneg hnn)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz
  intro S hS hNS
  have h1 := hall S (mem_range.mpr hS)
  have h2 : (N S) ^ 2 ≠ 0 := pow_ne_zero 2 hNS
  have h3 : ((3 : ℤ) - card n S) = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h h2
  have : ((card n S : ℕ) : ℤ) = 3 := by linarith
  exact_mod_cast this

/-- **`F 11`**: there is no 11-variable solution of the finite problem. -/
theorem F_eleven : F 11 := by
  rintro ⟨N, hsol⟩
  have hbk := bookkeeping (n := 11) hsol
  have hexc := excess_nonneg (n := 11) hsol
  have hbk' : ∑ v ∈ range 11, (mass 11 N v - 4) +
      ∑ S ∈ range (2 ^ 11), ((3 : ℤ) - card 11 S) * (N S) ^ 2 = 4 := by
    rw [hbk]; norm_num
  -- the δ = 4 branch: the excess vanishes, so `N` is cubic
  have hcub4 : (4 : ℤ) ≤ ∑ v ∈ range 11, (mass 11 N v - 4) → False := by
    intro hge
    refine eleven_delta_zero hsol (cubic_of_excess_le_zero hsol ?_)
    linarith
  have hterm : ∀ u ∈ range 11, (0 : ℤ) ≤ mass 11 N u - 4 := by
    intro u hu
    have := four_le_mass hsol (mem_range.mp hu)
    omega
  by_cases hall : ∀ v, v < 11 → mass 11 N v = 4
  · exact eleven_delta_four hsol hall
  push_neg at hall
  obtain ⟨v, hv, hvne⟩ := hall
  have hvc := mass_cases hsol le_rfl hv
  by_cases hrest : ∀ w, w < 11 → w ≠ v → mass 11 N w = 4
  · rcases hvc with h4 | h6 | h8
    · exact hvne h4
    · exact eleven_delta_two hsol hv h6 hrest
    · refine hcub4 ?_
      have hle := Finset.single_le_sum hterm (mem_range.mpr hv)
      rw [h8] at hle
      linarith
  · push_neg at hrest
    obtain ⟨w, hw, hwv, hwne⟩ := hrest
    have hwc := mass_cases hsol le_rfl hw
    refine hcub4 ?_
    have hsub : ({v, w} : Finset ℕ) ⊆ range 11 := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact mem_range.mpr (by omega)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i hi _ => hterm i hi)
    rw [Finset.sum_pair (Ne.symm hwv)] at hle
    omega

/-- both endpoints of the certificate in one statement -/
theorem F_eleven_and_twelve : F 11 ∧ F 12 := ⟨F_eleven, F_twelve⟩

end R3
