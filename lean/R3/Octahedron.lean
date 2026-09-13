import R3.Cycle
/-!
# Step 3 of R3_upper_bound.md, topology-free: the link structure as a relation on vertices

A support set of a 12-variable solution is a triple `tri a b c = 2^a ||| 2^b ||| 2^c`
(`exists_tri_of_card_three`).  `twelve_link_cycle` is repackaged as `twelve_link_struct`:
at every vertex `v` there are four distinct vertices `p q r s` (all `< 12`, all `≠ v`,
bundled in `Cyc v p q r s`) such that for all `x y < 12` different from `v`
`N (tri v x y) ≠ 0 ↔ Edge p q r s x y`, where `Edge p q r s x y` says that `{x, y}` is one of
the four edges `pq, qr, rs, sp` of the 4-cycle (`LinkIs N v p q r s`).

Everything after this point is combinatorics of the relation `Edge`, discharged by `omega`.
-/
namespace R3
open Finset

/-! ## Triples as bitmasks -/

/-- bitmask of the triple {a, b, c} -/
def tri (a b c : ℕ) : ℕ := 2 ^ a ||| 2 ^ b ||| 2 ^ c

lemma testBit_tri (a b c j : ℕ) :
    (tri a b c).testBit j = (decide (a = j) || decide (b = j) || decide (c = j)) := by
  simp [tri, Nat.testBit_or, Nat.testBit_two_pow]

lemma mem_tri_iff {a b c j : ℕ} : (tri a b c).testBit j = true ↔ j = a ∨ j = b ∨ j = c := by
  rw [testBit_tri]; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega

lemma tri_lt {n a b c : ℕ} (ha : a < n) (hb : b < n) (hc : c < n) : tri a b c < 2 ^ n :=
  Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) ha)
    (Nat.pow_lt_pow_right (by norm_num) hb)) (Nat.pow_lt_pow_right (by norm_num) hc)

/-- two triples with the same members are equal -/
lemma tri_ext {a b c a' b' c' : ℕ}
    (h : ∀ j, (j = a ∨ j = b ∨ j = c) ↔ (j = a' ∨ j = b' ∨ j = c')) :
    tri a b c = tri a' b' c' := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Bool.eq_iff_iff, mem_tri_iff, mem_tri_iff]; exact h j

lemma tri_xor_two_pow {v p q : ℕ} (hp : p ≠ v) (hq : q ≠ v) :
    tri v p q ^^^ 2 ^ v = pair p q := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor, testBit_tri, testBit_pair, Nat.testBit_two_pow]
  by_cases h1 : v = j <;> by_cases h2 : p = j <;> by_cases h3 : q = j <;>
    simp [h1, h2, h3] <;> omega

lemma pair_xor_two_pow {v p q : ℕ} (hp : p ≠ v) (hq : q ≠ v) :
    pair p q ^^^ 2 ^ v = tri v p q := by
  rw [← tri_xor_two_pow hp hq, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- a bitmask below `2^n` with exactly three bits (below `n`) is a triple -/
lemma exists_tri_of_card_three {n T : ℕ} (hT : T < 2 ^ n) (h3 : card n T = 3) :
    ∃ a b c, a < n ∧ b < n ∧ c < n ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ T = tri a b c := by
  unfold card at h3
  obtain ⟨a, b, c, hab, hac, hbc, hf⟩ := card_eq_three.mp h3
  have hmem : ∀ j, T.testBit j = true ↔ j = a ∨ j = b ∨ j = c := by
    intro j
    constructor
    · intro hj
      have hjn : j < n := by
        by_contra hc; push_neg at hc
        rw [testBit_eq_false_of_lt hT hc] at hj; exact Bool.false_ne_true hj
      have : j ∈ (range n).filter (fun i => T.testBit i) :=
        mem_filter.mpr ⟨mem_range.mpr hjn, hj⟩
      rw [hf] at this; simpa using this
    · intro hj
      have : j ∈ (range n).filter (fun i => T.testBit i) := by rw [hf]; simpa using hj
      exact (mem_filter.mp this).2
  have hlt : ∀ j, (j = a ∨ j = b ∨ j = c) → j < n := by
    intro j hj
    have : j ∈ (range n).filter (fun i => T.testBit i) := by rw [hf]; simpa using hj
    exact mem_range.mp (mem_filter.mp this).1
  refine ⟨a, b, c, hlt a (by simp), hlt b (by simp), hlt c (by simp), hab, hac, hbc, ?_⟩
  apply Nat.eq_of_testBit_eq; intro j
  rw [Bool.eq_iff_iff, hmem j, mem_tri_iff]

/-! ## Edges of a 4-cycle -/

/-- `{x, y}` is an edge of the 4-cycle p-q-r-s-p -/
def Edge (p q r s x y : ℕ) : Prop :=
  (x = p ∧ y = q) ∨ (x = q ∧ y = p) ∨ (x = q ∧ y = r) ∨ (x = r ∧ y = q) ∨
  (x = r ∧ y = s) ∨ (x = s ∧ y = r) ∨ (x = s ∧ y = p) ∨ (x = p ∧ y = s)

lemma onCycle_pair_iff {p q r s x y : ℕ} : OnCycle p q r s (pair x y) ↔ Edge p q r s x y := by
  unfold OnCycle Edge
  rw [pair_eq_iff, pair_eq_iff, pair_eq_iff, pair_eq_iff]
  tauto

/-- `p q r s` are four distinct vertices `< 12`, all different from `v` -/
def Cyc (v p q r s : ℕ) : Prop :=
  p < 12 ∧ q < 12 ∧ r < 12 ∧ s < 12 ∧ p ≠ v ∧ q ≠ v ∧ r ≠ v ∧ s ≠ v ∧
  p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s

/-- the support triples at `v` are exactly `v` plus an edge of the cycle p-q-r-s-p -/
def LinkIs (N : ℕ → ℤ) (v p q r s : ℕ) : Prop :=
  ∀ x y, x < 12 → y < 12 → x ≠ v → y ≠ v → (N (tri v x y) ≠ 0 ↔ Edge p q r s x y)

/-- n = 12: at every vertex `v` the support is `v` plus the edges of a 4-cycle on four
vertices `p q r s` distinct from `v`. -/
theorem twelve_link_struct {N : ℕ → ℤ} (hsol : IsSol 12 N) {v : ℕ} (hv : v < 12) :
    ∃ p q r s, Cyc v p q r s ∧ LinkIs N v p q r s := by
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, hcyc⟩ := twelve_link_cycle hsol hv
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs, -, -, -⟩ := twelve_link hsol hv
  have h2v : 2 ^ v < 2 ^ 12 := Nat.pow_lt_pow_right (by norm_num) hv
  -- every edge of the cycle is attained by a support set
  have hex : ∀ E, OnCycle p q r s E → ∃ S ∈ supp 12 N v, S ^^^ 2 ^ v = E := by
    intro E hE
    have hinj : Function.Injective (fun S : ℕ => S ^^^ 2 ^ v) := by
      intro x y h
      have := congrArg (fun z => z ^^^ 2 ^ v) h
      simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this
    have hsub : (supp 12 N v).image (fun S => S ^^^ 2 ^ v) ⊆
        {pair p q, pair q r, pair r s, pair s p} := by
      intro E hE
      rw [mem_image] at hE
      obtain ⟨S, hS, rfl⟩ := hE
      have := hcyc S hS
      unfold OnCycle at this
      simp only [mem_insert, mem_singleton]; exact this
    have hcard : ({pair p q, pair q r, pair r s, pair s p} : Finset ℕ).card ≤
        ((supp 12 N v).image (fun S => S ^^^ 2 ^ v)).card := by
      rw [card_image_of_injective _ hinj, hs, card_insert_of_notMem (by simp [hab, hac, had]),
        card_insert_of_notMem (by simp [hbc, hbd]), card_pair hcd]
      exact card_le_four
    have heq := eq_of_subset_of_card_le hsub hcard
    have hEm : E ∈ ({pair p q, pair q r, pair r s, pair s p} : Finset ℕ) := by
      unfold OnCycle at hE
      simp only [mem_insert, mem_singleton]; exact hE
    rw [← heq, mem_image] at hEm
    exact hEm
  -- the cycle vertices are < 12 and ≠ v
  have hvert : ∀ x y, OnCycle p q r s (pair x y) → x < 12 ∧ x ≠ v := by
    intro x y h
    obtain ⟨S, hS, hE⟩ := hex _ h
    obtain ⟨hlt, hb, -⟩ := mem_supp.mp hS
    have hx : (pair x y).testBit x = true := mem_pair_iff.mpr (Or.inl rfl)
    rw [← hE] at hx
    constructor
    · by_contra hc; push_neg at hc
      rw [testBit_eq_false_of_lt (Nat.xor_lt_two_pow hlt h2v) hc] at hx
      exact Bool.false_ne_true hx
    · rintro rfl
      rw [link_testBit_self S x hb] at hx
      exact Bool.false_ne_true hx
  have hp := hvert p q (Or.inl rfl)
  have hq := hvert q r (Or.inr (Or.inl rfl))
  have hr := hvert r s (Or.inr (Or.inr (Or.inl rfl)))
  have hs' := hvert s p (Or.inr (Or.inr (Or.inr rfl)))
  refine ⟨p, q, r, s, ⟨hp.1, hq.1, hr.1, hs'.1, hp.2, hq.2, hr.2, hs'.2,
    hpq, hpr, hps, hqr, hqs, hrs⟩, ?_⟩
  intro x y hx hy hxv hyv
  constructor
  · intro hN
    have hS : tri v x y ∈ supp 12 N v :=
      mem_supp.mpr ⟨tri_lt hv hx hy, mem_tri_iff.mpr (Or.inl rfl), hN⟩
    have := hcyc _ hS
    rw [tri_xor_two_pow hxv hyv] at this
    exact onCycle_pair_iff.mp this
  · intro hE
    obtain ⟨S, hS, hSE⟩ := hex _ (onCycle_pair_iff.mpr hE)
    have : S = tri v x y := by
      have := congrArg (fun z => z ^^^ 2 ^ v) hSE
      simp only at this
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, pair_xor_two_pow hxv hyv] at this
      exact this
    rw [← this]
    exact (mem_supp.mp hS).2.2

end R3
