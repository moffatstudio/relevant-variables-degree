import R3.Mass
import R3.Link
/-!
# The 12-variable case: Step 1 of R3_upper_bound.md

For a solution on 12 variables the bookkeeping identity `e + δ = 48 - 4·12 = 0` with both
summands non-negative forces
* every mass to be exactly 4                                   (`twelve_mass_four`),
* every set with nonzero coefficient to have exactly 3 elements (`twelve_card_three`),
* hence every link set at every vertex to be a pair            (`twelve_link_card_two`),
and every coefficient is ±1 (`twelve_coeff_pm`).  What is *not* yet formalised: links are
4-cycles, the closure into two octahedra, and the disjoint-sum contradiction (F(12)).
-/
namespace R3
open Finset

lemma mass_sub_four_nonneg {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n) :
    0 ≤ mass n N v - 4 := by
  have := four_le_mass hsol hv; linarith

lemma delta_term_nonneg {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {S : ℕ} (hS : S < 2 ^ n) :
    0 ≤ ((3 : ℤ) - card n S) * (N S) ^ 2 := by
  by_cases h : 3 < card n S
  · rw [hsol.1 S hS h]; simp
  · push_neg at h
    apply mul_nonneg _ (sq_nonneg _)
    have : (card n S : ℤ) ≤ 3 := by exact_mod_cast h
    linarith

/-- n = 12: the excess `e = ∑ (mass v - 4)` vanishes -/
lemma twelve_excess_zero {N : ℕ → ℤ} (hsol : IsSol 12 N) :
    ∑ v ∈ range 12, (mass 12 N v - 4) = 0 := by
  have hb := bookkeeping hsol
  have hA : 0 ≤ ∑ S ∈ range (2 ^ 12), ((3 : ℤ) - card 12 S) * (N S) ^ 2 :=
    sum_nonneg (fun S hS => delta_term_nonneg hsol (mem_range.mp hS))
  have h0 : 0 ≤ ∑ v ∈ range 12, (mass 12 N v - 4) :=
    sum_nonneg (fun v hv => mass_sub_four_nonneg hsol (mem_range.mp hv))
  simp only [Nat.cast_ofNat] at hb
  linarith

/-- n = 12: the lower-order weight `δ = ∑ (3 - |S|) n_S²` vanishes -/
lemma twelve_delta_zero {N : ℕ → ℤ} (hsol : IsSol 12 N) :
    ∑ S ∈ range (2 ^ 12), ((3 : ℤ) - card 12 S) * (N S) ^ 2 = 0 := by
  have hb := bookkeeping hsol
  have hA : 0 ≤ ∑ S ∈ range (2 ^ 12), ((3 : ℤ) - card 12 S) * (N S) ^ 2 :=
    sum_nonneg (fun S hS => delta_term_nonneg hsol (mem_range.mp hS))
  have h0 : 0 ≤ ∑ v ∈ range 12, (mass 12 N v - 4) :=
    sum_nonneg (fun v hv => mass_sub_four_nonneg hsol (mem_range.mp hv))
  simp only [Nat.cast_ofNat] at hb
  linarith

/-- n = 12: every vertex has mass exactly 4 -/
theorem twelve_mass_four {N : ℕ → ℤ} (hsol : IsSol 12 N) {v : ℕ} (hv : v < 12) :
    mass 12 N v = 4 := by
  have hE := twelve_excess_zero hsol
  have := (sum_eq_zero_iff_of_nonneg
    (fun v hv => mass_sub_four_nonneg hsol (mem_range.mp hv))).mp hE v (mem_range.mpr hv)
  linarith

/-- n = 12: every set with nonzero coefficient has exactly three elements -/
theorem twelve_card_three {N : ℕ → ℤ} (hsol : IsSol 12 N) {S : ℕ} (hS : S < 2 ^ 12)
    (hN : N S ≠ 0) : card 12 S = 3 := by
  have hD := twelve_delta_zero hsol
  have := (sum_eq_zero_iff_of_nonneg
    (fun S hS => delta_term_nonneg hsol (mem_range.mp hS))).mp hD S (mem_range.mpr hS)
  rcases mul_eq_zero.mp this with h | h
  · have h3 : card 12 S ≤ 3 := by
      by_contra hc; push_neg at hc; exact hN (hsol.1 S hS hc)
    have : (card 12 S : ℤ) = 3 := by linarith
    exact_mod_cast this
  · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hN

/-- n = 12: every coefficient in a support is ±1 -/
theorem twelve_coeff_pm {N : ℕ → ℤ} (hsol : IsSol 12 N) {v S : ℕ} (hv : v < 12)
    (hS : S ∈ supp 12 N v) : N S = 1 ∨ N S = -1 :=
  mass_four_pm hsol hv (twelve_mass_four hsol hv) S hS

/-- n = 12: every link set is a pair -/
theorem twelve_link_card_two {N : ℕ → ℤ} (hsol : IsSol 12 N) {v S : ℕ} (hv : v < 12)
    (hS : S ∈ supp 12 N v) : card 12 (S ^^^ 2 ^ v) = 2 := by
  obtain ⟨hlt, hb, hN⟩ := mem_supp.mp hS
  have h3 := twelve_card_three hsol hlt hN
  have h := card_xor_two_pow hv hb
  omega

/-- n = 12: at every vertex the support is four sets of size 3, coefficients ±1, link
sets four distinct pairs with xor 0, sign product +1 -/
theorem twelve_link {N : ℕ → ℤ} (hsol : IsSol 12 N) {v : ℕ} (hv : v < 12) :
    ∃ a b c d : ℕ, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      supp 12 N v = {a, b, c, d} ∧
      (∀ S ∈ ({a, b, c, d} : Finset ℕ), S < 2 ^ 12 ∧ S.testBit v = true ∧
          (N S = 1 ∨ N S = -1) ∧ card 12 S = 3 ∧ card 12 (S ^^^ 2 ^ v) = 2) ∧
      (a ^^^ 2 ^ v) ^^^ (b ^^^ 2 ^ v) ^^^ (c ^^^ 2 ^ v) ^^^ (d ^^^ 2 ^ v) = 0 ∧
      N a * N b * N c * N d = 1 := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs, hall, hxor, hprod⟩ :=
    mass_four_link hsol hv (twelve_mass_four hsol hv)
  refine ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs, ?_, hxor, hprod⟩
  intro S hS
  obtain ⟨hlt, hb, hpm, -, -, -⟩ := hall S hS
  have hS' : S ∈ supp 12 N v := by rw [hs]; exact hS
  exact ⟨hlt, hb, hpm, twelve_card_three hsol hlt (mem_supp.mp hS').2.2,
    twelve_link_card_two hsol hv hS'⟩

end R3
