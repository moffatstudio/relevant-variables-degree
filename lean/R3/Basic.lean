import R3.Statement
/-!
# Pointwise consequences of the finite statement

`chi n S x = (-1)^{|S ∩ x|}` (bits below `n`), `evalF n N x = ∑_S n_S χ_S(x)` (= 4 f_N(x)).
* (i)+(ii) ⇒ `evalF n N x ^ 2 = 16` for every `x`  (`evalF_sq`).
* E1: the link `linkVal n N v x = ∑_{S ∋ v} n_S χ_{S∖v}(x)` takes values in {0, ±4} (`linkVal_mem`).
* the mass `mass n N v = ∑_{S ∋ v} n_S²` is even (`two_dvd_mass`) and ≥ 4 (`four_le_mass`),
  and `∑_v mass v ≤ 48` (`sum_mass_le`).
* mass 4 ⇒ exactly four coefficients ±1 whose sets xor to 0 and whose product is 1 (`mass_four`).
-/
namespace R3
open Finset

/-- character χ_S(x), product over the bits `i < n` of `(-1)^{[i ∈ S ∧ i ∈ x]}` -/
def chi : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 1
  | n + 1, S, x => chi n S x * (if S.testBit n && x.testBit n then -1 else 1)

lemma chi_succ (n S x : ℕ) :
    chi (n + 1) S x = chi n S x * (if S.testBit n && x.testBit n then -1 else 1) := rfl

lemma chi_comm (n S x : ℕ) : chi n S x = chi n x S := by
  induction n with
  | zero => rfl
  | succ n ih => rw [chi_succ, chi_succ, ih, Bool.and_comm]

lemma chi_mul (n S T x : ℕ) : chi n S x * chi n T x = chi n (S ^^^ T) x := by
  induction n with
  | zero => simp [chi]
  | succ n ih =>
    rw [chi_succ, chi_succ, chi_succ, ← ih, Nat.testBit_xor]
    cases S.testBit n <;> cases T.testBit n <;> cases x.testBit n <;> simp

lemma chi_mul_right (n S x y : ℕ) : chi n S x * chi n S y = chi n S (x ^^^ y) := by
  rw [chi_comm n S x, chi_comm n S y, chi_comm n S, chi_mul]

lemma chi_zero_left (n x : ℕ) : chi n 0 x = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chi_succ, ih, Nat.zero_testBit]

lemma chi_zero_right (n S : ℕ) : chi n S 0 = 1 := by rw [chi_comm, chi_zero_left]

lemma chi_eq_or (n S x : ℕ) : chi n S x = 1 ∨ chi n S x = -1 := by
  induction n with
  | zero => left; rfl
  | succ n ih =>
    rw [chi_succ]
    rcases ih with h | h <;> rw [h] <;> split_ifs <;> simp

lemma chi_sq (n S x : ℕ) : chi n S x * chi n S x = 1 := by
  rcases chi_eq_or n S x with h | h <;> rw [h] <;> norm_num

lemma chi_two_pow_of_le (m e x : ℕ) (h : m ≤ e) : chi m (2 ^ e) x = 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [chi_succ, ih (by omega), Nat.testBit_two_pow_of_ne (by omega)]; simp

/-- χ_{2^v}(x) = (-1)^{[v ∈ x]} for v < n -/
lemma chi_two_pow (n v x : ℕ) (hv : v < n) :
    chi n (2 ^ v) x = if x.testBit v then -1 else 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [chi_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h | h
    · rw [ih h, Nat.testBit_two_pow_of_ne (by omega)]; simp
    · rw [h, chi_two_pow_of_le n n x le_rfl, Nat.testBit_two_pow_self]; simp

lemma chi_two_pow_right (n v S : ℕ) (hv : v < n) :
    chi n S (2 ^ v) = if S.testBit v then -1 else 1 := by
  rw [chi_comm, chi_two_pow n v S hv]

lemma testBit_eq_false_of_lt {W n j : ℕ} (hW : W < 2 ^ n) (hj : n ≤ j) : W.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hW (Nat.pow_le_pow_right (by norm_num) hj))

/-- a character that is identically 1 on the points 2^j (j < n) is trivial (for `W < 2^n`) -/
lemma eq_zero_of_chi_two_pow (n W : ℕ) (hW : W < 2 ^ n)
    (h : ∀ j, j < n → chi n W (2 ^ j) = 1) : W = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · have := h j hj
    rw [chi_two_pow_right n j W hj] at this
    rw [Nat.zero_testBit]
    by_cases hb : W.testBit j = true
    · rw [if_pos hb] at this; norm_num at this
    · rw [if_neg hb] at this; simpa using hb
  · rw [testBit_eq_false_of_lt hW (by omega), Nat.zero_testBit]

/-! ## The function 4 f_N and its square -/

/-- `evalF n N x = ∑_{S<2^n} n_S χ_S(x)`  (this is 4 f_N(x)) -/
def evalF (n : ℕ) (N : ℕ → ℤ) (x : ℕ) : ℤ := ∑ S ∈ range (2 ^ n), N S * chi n S x

lemma xor_mem_range {n S T : ℕ} (hS : S ∈ range (2 ^ n)) (hT : T ∈ range (2 ^ n)) :
    S ^^^ T ∈ range (2 ^ n) := by
  rw [mem_range] at *; exact Nat.xor_lt_two_pow hS hT

/-- (i)+(ii) ⇒ (4 f_N(x))² = 16 at every point x -/
theorem evalF_sq (n : ℕ) (N : ℕ → ℤ) (h1 : CondI n N) (h2 : CondII n N) (x : ℕ) :
    evalF n N x ^ 2 = 16 := by
  unfold evalF
  have hx : ∀ S ∈ range (2 ^ n), ∀ T ∈ range (2 ^ n),
      N S * chi n S x * (N T * chi n T x) =
      ∑ U ∈ range (2 ^ n), (if S ^^^ T = U then N S * N T else 0) * chi n U x := by
    intro S hS T hT
    simp_rw [ite_mul, zero_mul]
    rw [sum_ite_eq, if_pos (xor_mem_range hS hT), ← chi_mul]; ring
  rw [sq, sum_mul_sum, sum_congr rfl (fun S hS => sum_congr rfl (fun T hT => hx S hS T hT))]
  rw [sum_congr rfl (fun S _ => sum_comm), sum_comm]
  simp_rw [← sum_mul]
  rw [sum_eq_single 0]
  · rw [chi_zero_left, mul_one]
    have : ∀ S ∈ range (2 ^ n),
        (∑ T ∈ range (2 ^ n), if S ^^^ T = 0 then N S * N T else 0) = N S ^ 2 := by
      intro S hS
      simp_rw [Nat.xor_eq_zero]
      rw [sum_ite_eq, if_pos hS, sq]
    rw [sum_congr rfl this]; exact h1
  · intro U hU hU0
    rw [h2 U (Nat.pos_of_ne_zero hU0) (mem_range.mp hU), zero_mul]
  · intro h; exact absurd (mem_range.mpr (Nat.two_pow_pos n)) h

lemma sq_eq_16 {a : ℤ} (h : a ^ 2 = 16) : a = 4 ∨ a = -4 := by
  have : (a - 4) * (a + 4) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp this with h | h
  · left; linarith
  · right; linarith

/-! ## Links (E1) -/

/-- the link of v: `∑_{S ∋ v} n_S χ_{S ∖ v}(x)` (= 4 D_v f_N) -/
def linkVal (n : ℕ) (N : ℕ → ℤ) (v x : ℕ) : ℤ :=
  ∑ S ∈ range (2 ^ n), if S.testBit v then N S * chi n (S ^^^ 2 ^ v) x else 0

lemma evalF_sub_flip {n : ℕ} {N : ℕ → ℤ} {v : ℕ} (hv : v < n) (x : ℕ) :
    evalF n N x - evalF n N (x ^^^ 2 ^ v) = 2 * chi n (2 ^ v) x * linkVal n N v x := by
  unfold evalF linkVal
  rw [← sum_sub_distrib, mul_sum]
  apply sum_congr rfl; intro S _
  rw [← chi_mul_right, chi_two_pow_right n v S hv]
  have hc : chi n S x = chi n (S ^^^ 2 ^ v) x * chi n (2 ^ v) x := by
    rw [chi_mul, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  split_ifs with hb
  · rw [hc]; ring
  · ring

/-- E1: the link takes values in {0, 4, -4} -/
theorem linkVal_mem {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n) (x : ℕ) :
    linkVal n N v x = 0 ∨ linkVal n N v x = 4 ∨ linkVal n N v x = -4 := by
  obtain ⟨_, h1, h2, _⟩ := hsol
  have hA := sq_eq_16 (evalF_sq n N h1 h2 x)
  have hB := sq_eq_16 (evalF_sq n N h1 h2 (x ^^^ 2 ^ v))
  have hd := evalF_sub_flip (N := N) hv x
  rcases chi_eq_or n (2 ^ v) x with hc | hc <;> rw [hc] at hd <;>
  rcases hA with hA | hA <;> rcases hB with hB | hB <;> rw [hA, hB] at hd <;> omega

/-! ## Masses -/

/-- mass of v: `∑_{S ∋ v} n_S²` -/
def mass (n : ℕ) (N : ℕ → ℤ) (v : ℕ) : ℤ :=
  ∑ S ∈ range (2 ^ n), if S.testBit v then (N S) ^ 2 else 0

/-- the sets containing v with nonzero coefficient -/
def supp (n : ℕ) (N : ℕ → ℤ) (v : ℕ) : Finset ℕ :=
  (range (2 ^ n)).filter (fun S => S.testBit v ∧ N S ≠ 0)

lemma mem_supp {n : ℕ} {N : ℕ → ℤ} {v S : ℕ} :
    S ∈ supp n N v ↔ S < 2 ^ n ∧ S.testBit v = true ∧ N S ≠ 0 := by
  simp [supp, mem_filter, mem_range]

lemma mass_eq_sum_supp (n : ℕ) (N : ℕ → ℤ) (v : ℕ) :
    mass n N v = ∑ S ∈ supp n N v, (N S) ^ 2 := by
  unfold mass supp
  rw [sum_filter]
  apply sum_congr rfl; intro S _
  by_cases hb : S.testBit v = true <;> by_cases hN : N S = 0 <;> simp [hb, hN]

lemma linkVal_eq_sum_supp (n : ℕ) (N : ℕ → ℤ) (v x : ℕ) :
    linkVal n N v x = ∑ S ∈ supp n N v, N S * chi n (S ^^^ 2 ^ v) x := by
  unfold linkVal supp
  rw [sum_filter]
  apply sum_congr rfl; intro S _
  by_cases hb : S.testBit v = true <;> by_cases hN : N S = 0 <;> simp [hb, hN]

lemma mass_nonneg (n : ℕ) (N : ℕ → ℤ) (v : ℕ) : 0 ≤ mass n N v := by
  unfold mass; apply sum_nonneg; intro S _; split_ifs <;> positivity

/-- the mass is even -/
theorem two_dvd_mass {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n) :
    2 ∣ mass n N v := by
  have hL := linkVal_mem hsol hv 0
  have : mass n N v - linkVal n N v 0 =
      ∑ S ∈ range (2 ^ n), if S.testBit v then N S * (N S - 1) else 0 := by
    unfold mass linkVal; rw [← sum_sub_distrib]; apply sum_congr rfl; intro S _
    rw [chi_zero_right]; split_ifs <;> ring
  have hdvd : (2 : ℤ) ∣ mass n N v - linkVal n N v 0 := by
    rw [this]; apply dvd_sum; intro S _; split_ifs
    · exact even_iff_two_dvd.mp (Int.even_mul_pred_self _)
    · exact dvd_zero _
  rcases hL with h | h | h <;> rw [h] at hdvd <;> omega

lemma one_le_sq_of_ne_zero {a : ℤ} (h : a ≠ 0) : 1 ≤ a ^ 2 := by
  rcases lt_or_gt_of_ne h with h | h <;> nlinarith

lemma pm_one_of_sq_le_three {a : ℤ} (h0 : a ≠ 0) (h : a ^ 2 ≤ 3) : a = 1 ∨ a = -1 := by
  have h1 : a ≤ 1 := by nlinarith
  have h2 : -1 ≤ a := by nlinarith
  omega

lemma supp_nonempty {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n) :
    (supp n N v).Nonempty := by
  obtain ⟨S, hS, hb, hN⟩ := hsol.2.2.2 v hv
  exact ⟨S, mem_supp.mpr ⟨hS, hb, hN⟩⟩

/-- two distinct sets `a ≠ b` below 2^n both containing v differ at a bit `j < n`, `j ≠ v` -/
lemma exists_diff_bit {n v a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (hav : a.testBit v = true) (hbv : b.testBit v = true) (hab : a ≠ b) :
    ∃ j, j < n ∧ j ≠ v ∧ a.testBit j ≠ b.testBit j := by
  by_contra hcon
  push_neg at hcon
  apply hab
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · by_cases hjv : j = v
    · subst hjv; rw [hav, hbv]
    · exact hcon j hj hjv
  · rw [testBit_eq_false_of_lt ha (by omega), testBit_eq_false_of_lt hb (by omega)]

lemma testBit_xor_two_pow_of_ne {S v j : ℕ} (hjv : j ≠ v) :
    (S ^^^ 2 ^ v).testBit j = S.testBit j := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_of_ne (Ne.symm hjv)]; simp

/-- E2 (weak form): every relevant variable has mass ≥ 4 -/
theorem four_le_mass {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n) :
    4 ≤ mass n N v := by
  by_contra hlt
  push_neg at hlt
  have hm := mass_eq_sum_supp n N v
  have hpm : ∀ S ∈ supp n N v, N S = 1 ∨ N S = -1 := by
    intro S hS
    have hle : (N S) ^ 2 ≤ mass n N v := by
      rw [hm]; exact single_le_sum (fun T _ => sq_nonneg (N T)) hS
    exact pm_one_of_sq_le_three (mem_supp.mp hS).2.2 (by omega)
  have hcard : ((supp n N v).card : ℤ) ≤ 3 := by
    have : (supp n N v).card • (1 : ℤ) ≤ ∑ S ∈ supp n N v, (N S) ^ 2 :=
      card_nsmul_le_sum _ _ _ (fun S hS => one_le_sq_of_ne_zero (mem_supp.mp hS).2.2)
    rw [nsmul_eq_mul, mul_one] at this; omega
  have hne := supp_nonempty hsol hv
  have hpos : 0 < (supp n N v).card := card_pos.mpr hne
  have hL := fun x => linkVal_mem hsol hv x
  have hLs := fun x => linkVal_eq_sum_supp n N v x
  -- card ∈ {1,2,3}
  have hc3 : (supp n N v).card = 1 ∨ (supp n N v).card = 2 ∨ (supp n N v).card = 3 := by omega
  rcases hc3 with hc | hc | hc
  · obtain ⟨a, ha⟩ := card_eq_one.mp hc
    have h0 := hL 0; rw [hLs 0, ha, sum_singleton, chi_zero_right, mul_one] at h0
    have := hpm a (by rw [ha]; exact mem_singleton_self a)
    omega
  · obtain ⟨a, b, hab, hs⟩ := card_eq_two.mp hc
    have hma : a ∈ supp n N v := by rw [hs]; simp
    have hmb : b ∈ supp n N v := by rw [hs]; simp
    have hpa := hpm a hma
    have hpb := hpm b hmb
    obtain ⟨ha, hav, -⟩ := mem_supp.mp hma
    obtain ⟨hb, hbv, -⟩ := mem_supp.mp hmb
    have h0 := hL 0; rw [hLs 0, hs, sum_pair hab, chi_zero_right, chi_zero_right] at h0
    obtain ⟨j, hj, hjv, hdiff⟩ := exists_diff_bit ha hb hav hbv hab
    have hx := hL (2 ^ j)
    rw [hLs (2 ^ j), hs, sum_pair hab, chi_two_pow_right n j _ hj, chi_two_pow_right n j _ hj,
      testBit_xor_two_pow_of_ne hjv, testBit_xor_two_pow_of_ne hjv] at hx
    cases hja : a.testBit j <;> cases hjb : b.testBit j <;> simp [hja, hjb] at hdiff hx <;> omega
  · obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := card_eq_three.mp hc
    have hpa := hpm a (by rw [hs]; simp)
    have hpb := hpm b (by rw [hs]; simp)
    have hpc := hpm c (by rw [hs]; simp)
    have h0 := hL 0
    rw [hLs 0, hs, sum_insert (by simp [hab, hac]), sum_pair hbc,
      chi_zero_right, chi_zero_right, chi_zero_right] at h0
    omega

/-- ∑_v mass v = ∑_S |S| n_S² -/
lemma sum_mass (n : ℕ) (N : ℕ → ℤ) :
    ∑ v ∈ range n, mass n N v = ∑ S ∈ range (2 ^ n), (card n S : ℤ) * (N S) ^ 2 := by
  unfold mass
  rw [sum_comm]
  apply sum_congr rfl; intro S _
  rw [← sum_filter, sum_const, nsmul_eq_mul]; rfl

theorem sum_mass_le {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) :
    ∑ v ∈ range n, mass n N v ≤ 48 := by
  rw [sum_mass]
  have h1 := hsol.2.1
  unfold CondI at h1
  calc ∑ S ∈ range (2 ^ n), (card n S : ℤ) * (N S) ^ 2
      ≤ ∑ S ∈ range (2 ^ n), 3 * (N S) ^ 2 := by
        apply sum_le_sum; intro S hS
        by_cases hc : 3 < card n S
        · rw [hsol.1 S (mem_range.mp hS) hc]; simp
        · push_neg at hc
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact_mod_cast hc
    _ = 48 := by rw [← mul_sum, h1]; norm_num

/-! ## Mass 4 -/

lemma four_pm_sum {a b c d : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1)
    (h : a + b + c + d = 0 ∨ a + b + c + d = 4 ∨ a + b + c + d = -4) :
    a * b * c * d = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> revert h <;> norm_num

lemma xor_two_pow_cancel (a b v : ℕ) : (a ^^^ 2 ^ v) ^^^ (b ^^^ 2 ^ v) = a ^^^ b := by
  rw [Nat.xor_comm b, ← Nat.xor_assoc, Nat.xor_assoc a, Nat.xor_self, Nat.xor_zero]

theorem mass_four_pm {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n)
    (h4 : mass n N v = 4) : ∀ S ∈ supp n N v, N S = 1 ∨ N S = -1 := by
  intro S hS
  have hm := mass_eq_sum_supp n N v
  by_contra hne
  have hN0 := (mem_supp.mp hS).2.2
  have hbig : 4 ≤ (N S) ^ 2 := by
    have : N S ≤ -2 ∨ 2 ≤ N S := by omega
    rcases this with h | h <;> nlinarith
  -- then S is the only element
  have hrest : ∑ T ∈ (supp n N v).erase S, (N T) ^ 2 = 0 := by
    have this : ∑ T ∈ (supp n N v).erase S, (N T) ^ 2 + (N S) ^ 2 =
        ∑ T ∈ supp n N v, (N T) ^ 2 := sum_erase_add _ _ hS
    rw [← hm, h4] at this
    have hnn : 0 ≤ ∑ T ∈ (supp n N v).erase S, (N T) ^ 2 := sum_nonneg (fun T _ => sq_nonneg _)
    omega
  have hsingle : supp n N v = {S} := by
    apply eq_singleton_iff_unique_mem.mpr
    refine ⟨hS, fun T hT => ?_⟩
    by_contra hTS
    have hTm : T ∈ (supp n N v).erase S := mem_erase.mpr ⟨hTS, hT⟩
    have := (sum_eq_zero_iff_of_nonneg (fun T _ => sq_nonneg (N T))).mp hrest T hTm
    exact (mem_supp.mp hT).2.2 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  have hL := linkVal_mem hsol hv 0
  rw [linkVal_eq_sum_supp, hsingle, sum_singleton, chi_zero_right, mul_one] at hL
  have hNS : (N S) ^ 2 = 4 := by rw [hm, hsingle, sum_singleton] at h4; exact h4
  have : N S = 2 ∨ N S = -2 := by
    have : (N S - 2) * (N S + 2) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  omega

theorem mass_four_card {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n)
    (h4 : mass n N v = 4) : (supp n N v).card = 4 := by
  have hm := mass_eq_sum_supp n N v
  have hpm := mass_four_pm hsol hv h4
  have : ∑ S ∈ supp n N v, (N S) ^ 2 = ∑ S ∈ supp n N v, (1 : ℤ) := by
    apply sum_congr rfl; intro S hS
    rcases hpm S hS with h | h <;> rw [h] <;> norm_num
  rw [this, sum_const, nsmul_eq_mul, mul_one, h4] at hm
  exact_mod_cast hm.symm

/-- mass 4: the four coefficient sets xor to 0 and the four coefficients have product 1 -/
theorem mass_four {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n)
    (h4 : mass n N v = 4) {a b c d : ℕ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hs : supp n N v = {a, b, c, d}) :
    a ^^^ b ^^^ c ^^^ d = 0 ∧ N a * N b * N c * N d = 1 := by
  have hpm := mass_four_pm hsol hv h4
  have hma : a ∈ supp n N v := by rw [hs]; simp
  have hmb : b ∈ supp n N v := by rw [hs]; simp
  have hmc : c ∈ supp n N v := by rw [hs]; simp
  have hmd : d ∈ supp n N v := by rw [hs]; simp
  have hpa := hpm a hma
  have hpb := hpm b hmb
  have hpc := hpm c hmc
  have hpd := hpm d hmd
  have hsum : ∀ x, linkVal n N v x =
      N a * chi n (a ^^^ 2 ^ v) x + N b * chi n (b ^^^ 2 ^ v) x +
      N c * chi n (c ^^^ 2 ^ v) x + N d * chi n (d ^^^ 2 ^ v) x := by
    intro x
    rw [linkVal_eq_sum_supp, hs, sum_insert (by simp [hab, hac, had]),
      sum_insert (by simp [hbc, hbd]), sum_pair hcd]; ring
  -- product of the four terms is 1 at every point
  have hprod : ∀ x, (N a * chi n (a ^^^ 2 ^ v) x) * (N b * chi n (b ^^^ 2 ^ v) x) *
      (N c * chi n (c ^^^ 2 ^ v) x) * (N d * chi n (d ^^^ 2 ^ v) x) = 1 := by
    intro x
    have hL := linkVal_mem hsol hv x
    rw [hsum x] at hL
    have t : ∀ e, (N e = 1 ∨ N e = -1) → N e * chi n (e ^^^ 2 ^ v) x = 1 ∨
        N e * chi n (e ^^^ 2 ^ v) x = -1 := by
      intro e he
      rcases he with he | he <;> rcases chi_eq_or n (e ^^^ 2 ^ v) x with hc | hc <;>
        rw [he, hc] <;> norm_num
    exact four_pm_sum (t a hpa) (t b hpb) (t c hpc) (t d hpd) hL
  have hchi : ∀ x, chi n (a ^^^ 2 ^ v) x * chi n (b ^^^ 2 ^ v) x *
      chi n (c ^^^ 2 ^ v) x * chi n (d ^^^ 2 ^ v) x = chi n (a ^^^ b ^^^ c ^^^ d) x := by
    intro x
    rw [chi_mul, chi_mul, chi_mul, xor_two_pow_cancel, Nat.xor_assoc, xor_two_pow_cancel,
      ← Nat.xor_assoc]
  have hprod' : ∀ x, N a * N b * N c * N d * chi n (a ^^^ b ^^^ c ^^^ d) x = 1 := by
    intro x; rw [← hchi x, ← hprod x]; ring
  have hN : N a * N b * N c * N d = 1 := by
    have := hprod' 0; rwa [chi_zero_right, mul_one] at this
  refine ⟨?_, hN⟩
  refine eq_zero_of_chi_two_pow n _ ?_ ?_
  · have ha := (mem_supp.mp hma).1
    have hb := (mem_supp.mp hmb).1
    have hc := (mem_supp.mp hmc).1
    have hd := (mem_supp.mp hmd).1
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ha hb) hc) hd
  · intro j _
    have := hprod' (2 ^ j); rwa [hN, one_mul] at this

end R3
