import R3.Basic
/-!
# Masses in a solution with ≥ 11 variables  (Lemma 1 of R3_equals_10.md)

* `mass_le_eight`: for n ≥ 11 every mass is ≤ 8 (from ∑ mass ≤ 48 and mass ≥ 4).
* `mass_cases`:    for n ≥ 11 every mass is 4, 6 or 8 (masses are even).
* `card_mass_ne_four_le_two`, `nine_mass_four`: for n = 11 at most two vertices have
  mass ≠ 4, i.e. at least nine vertices have mass exactly 4.
* `bookkeeping`: ∑_v (mass v - 4) + ∑_S (3 - |S|) n_S² = 48 - 4n  (= 4 for n = 11).
-/
namespace R3
open Finset

/-- ∑_{u<n} mass u ≥ mass v + 4 (n-1), hence mass v + 4(n-1) ≤ 48 -/
lemma mass_add_le {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n) :
    mass n N v + 4 * ((n : ℤ) - 1) ≤ 48 := by
  have hsum := sum_mass_le hsol
  have hv' : v ∈ range n := mem_range.mpr hv
  rw [← add_sum_erase (range n) _ hv'] at hsum
  have hrest : ∑ u ∈ (range n).erase v, (4 : ℤ) ≤ ∑ u ∈ (range n).erase v, mass n N u := by
    apply sum_le_sum; intro u hu
    exact four_le_mass hsol (mem_range.mp (mem_of_mem_erase hu))
  rw [sum_const, card_erase_of_mem hv', card_range, nsmul_eq_mul] at hrest
  have hc : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hc] at hrest
  linarith

/-- for n ≥ 11 every mass is at most 8 -/
theorem mass_le_eight {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hn : 11 ≤ n) {v : ℕ}
    (hv : v < n) : mass n N v ≤ 8 := by
  have h := mass_add_le hsol hv
  have : (11 : ℤ) ≤ n := by exact_mod_cast hn
  linarith

/-- Lemma 1: for n ≥ 11 every mass is 4, 6 or 8 -/
theorem mass_cases {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hn : 11 ≤ n) {v : ℕ}
    (hv : v < n) : mass n N v = 4 ∨ mass n N v = 6 ∨ mass n N v = 8 := by
  have h1 := four_le_mass hsol hv
  have h2 := mass_le_eight hsol hn hv
  have h3 := two_dvd_mass hsol hv
  omega

/-- in an 11-variable solution at most two vertices have mass ≠ 4 -/
theorem card_mass_ne_four_le_two {N : ℕ → ℤ} (hsol : IsSol 11 N) :
    ((range 11).filter fun v => ¬ mass 11 N v = 4).card ≤ 2 := by
  have hsum := sum_mass_le hsol
  rw [← sum_filter_add_sum_filter_not (range 11) (fun v => ¬ mass 11 N v = 4)] at hsum
  have hA : ∑ v ∈ (range 11).filter (fun v => ¬ mass 11 N v = 4), (6 : ℤ) ≤
      ∑ v ∈ (range 11).filter (fun v => ¬ mass 11 N v = 4), mass 11 N v := by
    apply sum_le_sum; intro v hv
    rw [mem_filter, mem_range] at hv
    have := mass_cases hsol le_rfl hv.1
    omega
  have hB : ∑ v ∈ (range 11).filter (fun v => ¬ ¬ mass 11 N v = 4), (4 : ℤ) ≤
      ∑ v ∈ (range 11).filter (fun v => ¬ ¬ mass 11 N v = 4), mass 11 N v := by
    apply sum_le_sum; intro v hv
    rw [mem_filter, mem_range] at hv
    exact four_le_mass hsol hv.1
  rw [sum_const, nsmul_eq_mul] at hA hB
  have hc := filter_card_add_filter_neg_card_eq_card (s := range 11)
    (fun v => ¬ mass 11 N v = 4)
  rw [card_range] at hc
  have hc' : (((range 11).filter fun v => ¬ mass 11 N v = 4).card : ℤ) +
      ((range 11).filter fun v => ¬ ¬ mass 11 N v = 4).card = 11 := by exact_mod_cast hc
  omega

/-- in an 11-variable solution at least nine vertices have mass exactly 4 -/
theorem nine_mass_four {N : ℕ → ℤ} (hsol : IsSol 11 N) :
    9 ≤ ((range 11).filter fun v => mass 11 N v = 4).card := by
  have h := card_mass_ne_four_le_two hsol
  have hc := filter_card_add_filter_neg_card_eq_card (s := range 11)
    (fun v => mass 11 N v = 4)
  rw [card_range] at hc
  omega

/-- there is a vertex of mass 4 (n = 11) -/
theorem exists_mass_four {N : ℕ → ℤ} (hsol : IsSol 11 N) :
    ∃ v, v < 11 ∧ mass 11 N v = 4 := by
  have h := nine_mass_four hsol
  have hne : ((range 11).filter fun v => mass 11 N v = 4).Nonempty := by
    apply card_pos.mp; omega
  obtain ⟨v, hv⟩ := hne
  rw [mem_filter, mem_range] at hv
  exact ⟨v, hv.1, hv.2⟩

/-- bookkeeping: e + δ = 48 - 4n where e = ∑_v (mass v - 4), δ = ∑_S (3 - |S|) n_S² -/
theorem bookkeeping {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) :
    ∑ v ∈ range n, (mass n N v - 4) +
      ∑ S ∈ range (2 ^ n), ((3 : ℤ) - card n S) * (N S) ^ 2 = 48 - 4 * n := by
  have h1 := hsol.2.1
  unfold CondI at h1
  have hm := sum_mass n N
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, hm]
  have : ∑ S ∈ range (2 ^ n), ((3 : ℤ) - card n S) * (N S) ^ 2 =
      3 * ∑ S ∈ range (2 ^ n), (N S) ^ 2 - ∑ S ∈ range (2 ^ n), (card n S : ℤ) * (N S) ^ 2 := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro S _; ring
  rw [this, h1]; ring

end R3
