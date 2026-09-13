import R3.LinkTypes
/-!
# The link of a mass-6 vertex  (Lemma 2(b) of R3_equals_10.md)

At a vertex `v` of mass 6 the support consists of exactly six sets, each with coefficient
`±1` (the pattern `{±2, ±1, ±1}` is impossible — this is the "no ±2 at mass 6" half of
Lemma 1's proof, confirmed by the referee brute force in `round2b_out_lemma1.txt`).  The six
link sets `S ^^^ 2^v` are distinct, of size ≤ 2, avoid `v`, xor to `0`, and the six
coefficients have product `-1`.
-/
namespace R3
open Finset

/-! ## Small arithmetic helpers -/

lemma sq_ne_two {a : ℤ} (h : a ^ 2 = 2) : False := by
  have h0 : a ≠ 0 := by rintro rfl; norm_num at h
  have := pm_one_of_sq_le_three h0 (by omega)
  rcases this with rfl | rfl <;> norm_num at h

lemma sq_eq_one_of {a : ℤ} (h0 : a ≠ 0) (h : a ^ 2 ≤ 1) : a = 1 ∨ a = -1 :=
  pm_one_of_sq_le_three h0 (by omega)

/-- six `±1`'s whose sum avoids `±2` and `±6` have product `-1` -/
lemma six_pm_sum {a b c d e f : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1) (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1)
    (h : a + b + c + d + e + f = 0 ∨ a + b + c + d + e + f = 4 ∨
      a + b + c + d + e + f = -4) :
    a * b * c * d * e * f = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
    revert h <;> norm_num

/-- `{±2, ±1, ±1}` never sums into `{0, ±4}` unless the two units agree -/
lemma two_one_one_agree {u0 u1 u2 : ℤ} (h0 : u0 = 2 ∨ u0 = -2) (h1 : u1 = 1 ∨ u1 = -1)
    (h2 : u2 = 1 ∨ u2 = -1)
    (h : u0 + u1 + u2 = 0 ∨ u0 + u1 + u2 = 4 ∨ u0 + u1 + u2 = -4) : u1 * u2 = 1 := by
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    revert h <;> norm_num

/-- the six copies of `2^v` cancel -/
lemma xor_two_pow_cancel6 (a b c d e f v : ℕ) :
    (a ^^^ 2 ^ v) ^^^ (b ^^^ 2 ^ v) ^^^ (c ^^^ 2 ^ v) ^^^ (d ^^^ 2 ^ v) ^^^
      (e ^^^ 2 ^ v) ^^^ (f ^^^ 2 ^ v) = a ^^^ b ^^^ c ^^^ d ^^^ e ^^^ f := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> cases c.testBit j <;> cases d.testBit j <;>
    cases e.testBit j <;> cases f.testBit j <;> cases (2 ^ v).testBit j <;> rfl

/-- a `Finset` of six elements, named -/
lemma card_eq_six {s : Finset ℕ} (h : s.card = 6) :
    ∃ a b c d e f, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧
      b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧ c ≠ d ∧ c ≠ e ∧ c ≠ f ∧
      d ≠ e ∧ d ≠ f ∧ e ≠ f ∧ s = {a, b, c, d, e, f} := by
  obtain ⟨a, t, hat, rfl, ht⟩ := card_eq_succ.mp h
  obtain ⟨b, u, hbu, rfl, hu⟩ := card_eq_succ.mp ht
  obtain ⟨c, d, e, f, hcd, hce, hcf, hde, hdf, hef, rfl⟩ := card_eq_four hu
  refine ⟨a, b, c, d, e, f, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcd, hce, hcf, hde, hdf,
    hef, rfl⟩
  · rintro rfl; exact hat (by simp)
  · rintro rfl; exact hat (by simp)
  · rintro rfl; exact hat (by simp)
  · rintro rfl; exact hat (by simp)
  · rintro rfl; exact hat (by simp)
  · rintro rfl; exact hbu (by simp)
  · rintro rfl; exact hbu (by simp)
  · rintro rfl; exact hbu (by simp)
  · rintro rfl; exact hbu (by simp)

/-! ## No `±2` coefficient at a mass-6 vertex -/

/-- **Lemma 1, second half.**  Every support coefficient at a mass-6 vertex is `±1`; the
pattern `{±2, ±1, ±1}` would force the two unit characters to agree identically. -/
theorem mass_six_pm {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n)
    (h6 : mass n N v = 6) : ∀ S ∈ supp n N v, N S = 1 ∨ N S = -1 := by
  intro S0 hS0
  by_contra hne
  have hm := mass_eq_sum_supp n N v
  have hN0 := (mem_supp.mp hS0).2.2
  have hbig : 4 ≤ (N S0) ^ 2 := by
    have : N S0 ≤ -2 ∨ 2 ≤ N S0 := by omega
    rcases this with h | h <;> nlinarith
  -- the other coefficients carry total square weight 6 - (N S0)^2
  have hsplit : ∑ T ∈ (supp n N v).erase S0, (N T) ^ 2 + (N S0) ^ 2 = 6 := by
    rw [sum_erase_add _ _ hS0, ← hm, h6]
  have hnn : 0 ≤ ∑ T ∈ (supp n N v).erase S0, (N T) ^ 2 :=
    sum_nonneg (fun T _ => sq_nonneg _)
  have hS0sq : (N S0) ^ 2 = 4 := by
    rcases lt_or_ge ((N S0) ^ 2) 5 with h | h
    · omega
    · -- (N S0)^2 ≥ 5 forces |N S0| ≥ 3, i.e. square ≥ 9 > 6
      exfalso
      have : N S0 ≤ -3 ∨ 3 ≤ N S0 := by
        by_contra hc
        push_neg at hc
        have h1 : -2 ≤ N S0 := by omega
        have h2 : N S0 ≤ 2 := by omega
        nlinarith
      rcases this with hx | hx <;> nlinarith
  have hrest : ∑ T ∈ (supp n N v).erase S0, (N T) ^ 2 = 2 := by omega
  -- each remaining coefficient has square ≥ 1, so there are exactly two of them
  have hge1 : ∀ T ∈ (supp n N v).erase S0, (1 : ℤ) ≤ (N T) ^ 2 := by
    intro T hT
    exact one_le_sq_of_ne_zero (mem_supp.mp (mem_of_mem_erase hT)).2.2
  have hcard : ((supp n N v).erase S0).card = 2 := by
    have hle : ((((supp n N v).erase S0).card : ℤ)) ≤ 2 := by
      calc ((((supp n N v).erase S0).card : ℤ))
          = ∑ T ∈ (supp n N v).erase S0, (1 : ℤ) := by
            rw [sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ∑ T ∈ (supp n N v).erase S0, (N T) ^ 2 := sum_le_sum hge1
        _ = 2 := hrest
    have hcle : ((supp n N v).erase S0).card ≤ 2 := by exact_mod_cast hle
    interval_cases h : ((supp n N v).erase S0).card
    · rw [card_eq_zero] at h; rw [h] at hrest; simp at hrest
    · rw [card_eq_one] at h
      obtain ⟨T, hT⟩ := h
      rw [hT, sum_singleton] at hrest
      exact absurd hrest (fun hh => sq_ne_two hh)
    · rfl
  obtain ⟨T1, T2, hT12, hTs⟩ := card_eq_two.mp hcard
  have hT1e : T1 ∈ (supp n N v).erase S0 := by rw [hTs]; simp
  have hT2e : T2 ∈ (supp n N v).erase S0 := by rw [hTs]; simp
  have hT1 : T1 ∈ supp n N v := mem_of_mem_erase hT1e
  have hT2 : T2 ∈ supp n N v := mem_of_mem_erase hT2e
  have hsq : (N T1) ^ 2 + (N T2) ^ 2 = 2 := by rw [hTs, sum_pair hT12] at hrest; exact hrest
  have hq1 : (1 : ℤ) ≤ (N T1) ^ 2 := one_le_sq_of_ne_zero (mem_supp.mp hT1).2.2
  have hq2 : (1 : ℤ) ≤ (N T2) ^ 2 := one_le_sq_of_ne_zero (mem_supp.mp hT2).2.2
  have hp1 : N T1 = 1 ∨ N T1 = -1 :=
    sq_eq_one_of (mem_supp.mp hT1).2.2 (by omega)
  have hp2 : N T2 = 1 ∨ N T2 = -1 :=
    sq_eq_one_of (mem_supp.mp hT2).2.2 (by omega)
  have hpm0 : N S0 = 2 ∨ N S0 = -2 := by
    have : (N S0 - 2) * (N S0 + 2) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  -- the support is exactly {S0, T1, T2}
  have hsupp : supp n N v = {S0, T1, T2} := by
    have h1 : (supp n N v).erase S0 = {T1, T2} := hTs
    have := insert_erase hS0
    rw [h1] at this
    exact this.symm
  have hS0T1 : S0 ≠ T1 := Ne.symm (ne_of_mem_erase hT1e)
  have hS0T2 : S0 ≠ T2 := Ne.symm (ne_of_mem_erase hT2e)
  -- expand the link value
  have hsum : ∀ x, linkVal n N v x =
      N S0 * chi n (S0 ^^^ 2 ^ v) x + N T1 * chi n (T1 ^^^ 2 ^ v) x +
        N T2 * chi n (T2 ^^^ 2 ^ v) x := by
    intro x
    rw [linkVal_eq_sum_supp, hsupp, sum_insert (by simp [hS0T1, hS0T2]), sum_pair hT12]
    ring
  have hunit : ∀ x, (N T1 * chi n (T1 ^^^ 2 ^ v) x) * (N T2 * chi n (T2 ^^^ 2 ^ v) x) = 1 := by
    intro x
    have hL := linkVal_mem hsol hv x
    rw [hsum x] at hL
    have t0 : N S0 * chi n (S0 ^^^ 2 ^ v) x = 2 ∨ N S0 * chi n (S0 ^^^ 2 ^ v) x = -2 := by
      rcases hpm0 with h | h <;> rcases chi_eq_or n (S0 ^^^ 2 ^ v) x with hc | hc <;>
        rw [h, hc] <;> norm_num
    have t : ∀ e, (N e = 1 ∨ N e = -1) → N e * chi n (e ^^^ 2 ^ v) x = 1 ∨
        N e * chi n (e ^^^ 2 ^ v) x = -1 := by
      intro e he
      rcases he with he | he <;> rcases chi_eq_or n (e ^^^ 2 ^ v) x with hc | hc <;>
        rw [he, hc] <;> norm_num
    exact two_one_one_agree t0 (t T1 hp1) (t T2 hp2) hL
  -- hence the character of T1 Δ T2 is constant 1, so T1 = T2
  have hchi : ∀ x, N T1 * N T2 * chi n (T1 ^^^ T2) x = 1 := by
    intro x
    have := hunit x
    rw [show N T1 * chi n (T1 ^^^ 2 ^ v) x * (N T2 * chi n (T2 ^^^ 2 ^ v) x)
        = N T1 * N T2 * (chi n (T1 ^^^ 2 ^ v) x * chi n (T2 ^^^ 2 ^ v) x) by ring,
      chi_mul, xor_two_pow_cancel] at this
    exact this
  have hNN : N T1 * N T2 = 1 := by
    have := hchi 0; rwa [chi_zero_right, mul_one] at this
  have hzero : T1 ^^^ T2 = 0 := by
    refine eq_zero_of_chi_two_pow n _ ?_ ?_
    · exact Nat.xor_lt_two_pow (mem_supp.mp hT1).1 (mem_supp.mp hT2).1
    · intro j _
      have := hchi (2 ^ j); rwa [hNN, one_mul] at this
  exact hT12 (xor_eq_of_xor_eq_zero hzero)

theorem mass_six_card {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n)
    (h6 : mass n N v = 6) : (supp n N v).card = 6 := by
  have hm := mass_eq_sum_supp n N v
  have hpm := mass_six_pm hsol hv h6
  have : ∑ S ∈ supp n N v, (N S) ^ 2 = ∑ S ∈ supp n N v, (1 : ℤ) := by
    apply sum_congr rfl; intro S hS
    rcases hpm S hS with h | h <;> rw [h] <;> norm_num
  rw [this, sum_const, nsmul_eq_mul, mul_one, h6] at hm
  exact_mod_cast hm.symm

/-- Lemma 2(b): the six support sets at a mass-6 vertex xor to `0` and their coefficients
have product `-1`. -/
theorem mass_six {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n)
    (h6 : mass n N v = 6) {a b c d e f : ℕ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hs : supp n N v = {a, b, c, d, e, f}) :
    a ^^^ b ^^^ c ^^^ d ^^^ e ^^^ f = 0 ∧ N a * N b * N c * N d * N e * N f = -1 := by
  have hpm := mass_six_pm hsol hv h6
  have hma : a ∈ supp n N v := by rw [hs]; simp
  have hmb : b ∈ supp n N v := by rw [hs]; simp
  have hmc : c ∈ supp n N v := by rw [hs]; simp
  have hmd : d ∈ supp n N v := by rw [hs]; simp
  have hme : e ∈ supp n N v := by rw [hs]; simp
  have hmf : f ∈ supp n N v := by rw [hs]; simp
  have hpa := hpm a hma
  have hpb := hpm b hmb
  have hpc := hpm c hmc
  have hpd := hpm d hmd
  have hpe := hpm e hme
  have hpf := hpm f hmf
  have hsum : ∀ x, linkVal n N v x =
      N a * chi n (a ^^^ 2 ^ v) x + N b * chi n (b ^^^ 2 ^ v) x +
      N c * chi n (c ^^^ 2 ^ v) x + N d * chi n (d ^^^ 2 ^ v) x +
      N e * chi n (e ^^^ 2 ^ v) x + N f * chi n (f ^^^ 2 ^ v) x := by
    intro x
    rw [linkVal_eq_sum_supp, hs, sum_insert (by simp [hab, hac, had, hae, haf]),
      sum_insert (by simp [hbc, hbd, hbe, hbf]), sum_insert (by simp [hcd, hce, hcf]),
      sum_insert (by simp [hde, hdf]), sum_pair hef]
    ring
  have hprod : ∀ x, (N a * chi n (a ^^^ 2 ^ v) x) * (N b * chi n (b ^^^ 2 ^ v) x) *
      (N c * chi n (c ^^^ 2 ^ v) x) * (N d * chi n (d ^^^ 2 ^ v) x) *
      (N e * chi n (e ^^^ 2 ^ v) x) * (N f * chi n (f ^^^ 2 ^ v) x) = -1 := by
    intro x
    have hL := linkVal_mem hsol hv x
    rw [hsum x] at hL
    have t : ∀ w, (N w = 1 ∨ N w = -1) → N w * chi n (w ^^^ 2 ^ v) x = 1 ∨
        N w * chi n (w ^^^ 2 ^ v) x = -1 := by
      intro w hw
      rcases hw with hw | hw <;> rcases chi_eq_or n (w ^^^ 2 ^ v) x with hc | hc <;>
        rw [hw, hc] <;> norm_num
    exact six_pm_sum (t a hpa) (t b hpb) (t c hpc) (t d hpd) (t e hpe) (t f hpf) hL
  have hchi : ∀ x, chi n (a ^^^ 2 ^ v) x * chi n (b ^^^ 2 ^ v) x *
      chi n (c ^^^ 2 ^ v) x * chi n (d ^^^ 2 ^ v) x * chi n (e ^^^ 2 ^ v) x *
      chi n (f ^^^ 2 ^ v) x = chi n (a ^^^ b ^^^ c ^^^ d ^^^ e ^^^ f) x := by
    intro x
    rw [chi_mul, chi_mul, chi_mul, chi_mul, chi_mul, xor_two_pow_cancel6]
  have hprod' : ∀ x, N a * N b * N c * N d * N e * N f *
      chi n (a ^^^ b ^^^ c ^^^ d ^^^ e ^^^ f) x = -1 := by
    intro x; rw [← hchi x, ← hprod x]; ring
  have hN : N a * N b * N c * N d * N e * N f = -1 := by
    have := hprod' 0; rwa [chi_zero_right, mul_one] at this
  refine ⟨?_, hN⟩
  refine eq_zero_of_chi_two_pow n _ ?_ ?_
  · have ha := (mem_supp.mp hma).1
    have hb := (mem_supp.mp hmb).1
    have hc := (mem_supp.mp hmc).1
    have hd := (mem_supp.mp hmd).1
    have he := (mem_supp.mp hme).1
    have hf := (mem_supp.mp hmf).1
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
      (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ha hb) hc) hd) he) hf
  · intro j _
    have h1 := hprod' (2 ^ j)
    rw [hN] at h1
    linarith

/-- **Lemma 2(b), packaged.**  The link of a mass-6 vertex consists of six distinct sets,
each containing `v` with coefficient `±1` and size ≤ 3, whose link sets have size ≤ 2,
avoid `v`, and xor to `0`; the six coefficients multiply to `-1`. -/
theorem mass_six_link {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n)
    (h6 : mass n N v = 6) :
    ∃ a b c d e f : ℕ,
      (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧
        c ≠ d ∧ c ≠ e ∧ c ≠ f ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f) ∧
      supp n N v = {a, b, c, d, e, f} ∧
      (∀ S ∈ ({a, b, c, d, e, f} : Finset ℕ), S < 2 ^ n ∧ S.testBit v = true ∧
          (N S = 1 ∨ N S = -1) ∧ card n S ≤ 3 ∧
          card n (S ^^^ 2 ^ v) ≤ 2 ∧ (S ^^^ 2 ^ v).testBit v = false) ∧
      (a ^^^ 2 ^ v) ^^^ (b ^^^ 2 ^ v) ^^^ (c ^^^ 2 ^ v) ^^^ (d ^^^ 2 ^ v) ^^^
        (e ^^^ 2 ^ v) ^^^ (f ^^^ 2 ^ v) = 0 ∧
      N a * N b * N c * N d * N e * N f = -1 := by
  obtain ⟨a, b, c, d, e, f, hab, hac, had, hae, haf, hbc, hbd, hbe, hbf, hcd, hce, hcf,
    hde, hdf, hef, hs⟩ := card_eq_six (mass_six_card hsol hv h6)
  obtain ⟨hxor, hprod⟩ := mass_six hsol hv h6 hab hac had hae haf hbc hbd hbe hbf hcd hce
    hcf hde hdf hef hs
  refine ⟨a, b, c, d, e, f, ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf, hcd, hce, hcf,
    hde, hdf, hef⟩, hs, ?_, ?_, hprod⟩
  · intro S hS
    rw [← hs] at hS
    obtain ⟨hlt, hbit, -⟩ := mem_supp.mp hS
    exact ⟨hlt, hbit, mass_six_pm hsol hv h6 S hS, card_le_three_of_mem_supp hsol hS,
      card_link_le_two hsol hv hS, link_testBit_self S v hbit⟩
  · rw [xor_two_pow_cancel6]; exact hxor

end R3
