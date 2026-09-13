import R3.Octahedron
/-!
# Link types L1..L4 (Lemma 2(a) of R3_equals_10.md) — the toolkit

The link of a mass-4 vertex is four distinct sets of size ≤ 2 whose xor is 0
(`mass_four_link`).  Lemma 2(a) says such a family is one of
* **L1** a 4-cycle of pairs `pq, qr, rs, sp`  (`four_pairs_cycle`, already proved);
* **L2** `∅, {a}, {b}, {a,b}`;
* **L3** `{a}, {b}, {a,c}, {b,c}`;
* **L4** `∅, {a,b}, {b,c}, {a,c}`.

This file contains the toolkit for that classification, all of it proved:
the trichotomy `card_le_two_cases` (a mask with ≤ 2 bits is `0`, `2^a` or `pair a b`),
the target predicate `LinkType` with its permutation lemmas, the triangle lemma
`three_pairs_triangle` (three distinct pairs with xor 0 are the edges of a triangle), and the
impossibility facts that rule out the remaining shapes.  The classification theorem `link_types` is proved at the end of this file.
-/
namespace R3
open Finset

/-! ## Reading off the members of a bitmask from its filter -/

/-- the bits of `T` below `2^n` are exactly the members of its filter -/
lemma testBit_iff_mem_filter {n T : ℕ} (hT : T < 2 ^ n) {s : Finset ℕ}
    (hf : (range n).filter (fun i => T.testBit i) = s) (j : ℕ) :
    T.testBit j = true ↔ j ∈ s := by
  constructor
  · intro hj
    have hjn : j < n := by
      by_contra hc; push_neg at hc
      rw [testBit_eq_false_of_lt hT hc] at hj; exact Bool.false_ne_true hj
    have : j ∈ (range n).filter (fun i => T.testBit i) :=
      mem_filter.mpr ⟨mem_range.mpr hjn, hj⟩
    rwa [hf] at this
  · intro hj
    have : j ∈ (range n).filter (fun i => T.testBit i) := by rw [hf]; exact hj
    exact (mem_filter.mp this).2

/-- members of the filter are `< n` -/
lemma lt_of_mem_filter {n T : ℕ} {s : Finset ℕ}
    (hf : (range n).filter (fun i => T.testBit i) = s) {j : ℕ} (hj : j ∈ s) : j < n := by
  have : j ∈ (range n).filter (fun i => T.testBit i) := by rw [hf]; exact hj
  exact mem_range.mp (mem_filter.mp this).1

/-- a bitmask below `2^n` with no bits below `n` is zero -/
lemma eq_zero_of_card_zero {n T : ℕ} (hT : T < 2 ^ n) (h : card n T = 0) : T = 0 := by
  unfold card at h
  rw [card_eq_zero] at h
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.zero_testBit]
  cases hb : T.testBit j with
  | false => rfl
  | true => exact absurd ((testBit_iff_mem_filter hT h j).mp hb) (by simp)

/-- a bitmask below `2^n` with exactly one bit is a power of two -/
lemma exists_two_pow_of_card_one {n T : ℕ} (hT : T < 2 ^ n) (h : card n T = 1) :
    ∃ a, a < n ∧ T = 2 ^ a := by
  unfold card at h
  obtain ⟨a, hf⟩ := card_eq_one.mp h
  refine ⟨a, lt_of_mem_filter hf (mem_singleton_self a), ?_⟩
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Bool.eq_iff_iff, testBit_iff_mem_filter hT hf j, Nat.testBit_two_pow]
  simp [eq_comm]

/-- **Trichotomy for link sets.**  A bitmask below `2^n` with at most two bits is empty,
a singleton, or a pair. -/
lemma card_le_two_cases {n T : ℕ} (hT : T < 2 ^ n) (h2 : card n T ≤ 2) :
    T = 0 ∨ (∃ a, a < n ∧ T = 2 ^ a) ∨
      (∃ a b, a < n ∧ b < n ∧ a ≠ b ∧ T = pair a b) := by
  interval_cases h : card n T
  · exact Or.inl (eq_zero_of_card_zero hT h)
  · exact Or.inr (Or.inl (exists_two_pow_of_card_one hT h))
  · obtain ⟨a, b, ha, hb, hab, hT'⟩ := exists_pair_of_card_two hT h
    exact Or.inr (Or.inr ⟨a, b, ha, hb, hab, hT'⟩)

/-! ## The four link types -/

/-- L2: `T` is one of `∅, {a}, {b}, {a,b}` -/
def IsL2 (a b T : ℕ) : Prop := T = 0 ∨ T = 2 ^ a ∨ T = 2 ^ b ∨ T = pair a b

/-- L3: `T` is one of `{a}, {b}, {a,c}, {b,c}` -/
def IsL3 (a b c T : ℕ) : Prop := T = 2 ^ a ∨ T = 2 ^ b ∨ T = pair a c ∨ T = pair b c

/-- L4: `T` is one of `∅, {a,b}, {b,c}, {a,c}` -/
def IsL4 (a b c T : ℕ) : Prop := T = 0 ∨ T = pair a b ∨ T = pair b c ∨ T = pair a c

/-- The conclusion of the classification: the four link sets fall into one of L1..L4. -/
def LinkType (T1 T2 T3 T4 : ℕ) : Prop :=
  (∃ p q r s, p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
      OnCycle p q r s T1 ∧ OnCycle p q r s T2 ∧ OnCycle p q r s T3 ∧ OnCycle p q r s T4) ∨
  (∃ a b, a ≠ b ∧ IsL2 a b T1 ∧ IsL2 a b T2 ∧ IsL2 a b T3 ∧ IsL2 a b T4) ∨
  (∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      IsL3 a b c T1 ∧ IsL3 a b c T2 ∧ IsL3 a b c T3 ∧ IsL3 a b c T4) ∨
  (∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      IsL4 a b c T1 ∧ IsL4 a b c T2 ∧ IsL4 a b c T3 ∧ IsL4 a b c T4)


/-! ## Triangles: three distinct pairs with xor 0 -/

lemma xor_eq_of_xor_eq_zero {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  have := congrArg (fun z => z ^^^ b) h
  simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] using this

lemma pair_xor_two_pow_left {a b : ℕ} (hab : a ≠ b) : pair a b ^^^ 2 ^ a = 2 ^ b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor, testBit_pair, Nat.testBit_two_pow, Nat.testBit_two_pow]
  by_cases h1 : a = j <;> by_cases h2 : b = j <;> simp [h1, h2] <;> omega

/-- two pairs sharing the vertex `a` xor to the pair of the other two vertices -/
lemma pair_xor_pair_left {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    pair a b ^^^ pair a c = pair b c := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor, testBit_pair, testBit_pair, testBit_pair]
  by_cases h1 : a = j <;> by_cases h2 : b = j <;> by_cases h3 : c = j <;>
    simp [h1, h2, h3] <;> omega

/-- **Three distinct pairs with xor 0 form a triangle.**  The conclusion is in the strong
form: the three given pairs are, in order, `xy`, `xz`, `yz` for three distinct vertices. -/
theorem three_pairs_triangle {a1 b1 a2 b2 a3 b3 : ℕ}
    (h1 : a1 ≠ b1) (h2 : a2 ≠ b2) (h3 : a3 ≠ b3)
    (d12 : pair a1 b1 ≠ pair a2 b2) (d13 : pair a1 b1 ≠ pair a3 b3)
    (hxor : pair a1 b1 ^^^ pair a2 b2 ^^^ pair a3 b3 = 0) :
    ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      pair a1 b1 = pair x y ∧ pair a2 b2 = pair x z ∧ pair a3 b3 = pair y z := by
  -- exactly one of the other two pairs contains `a1`
  have hb1 : (pair a1 b1).testBit a1 = true := mem_pair_iff.mpr (Or.inl rfl)
  have hzero : ((pair a1 b1 ^^^ pair a2 b2) ^^^ pair a3 b3).testBit a1 = false := by
    rw [hxor]; exact Nat.zero_testBit a1
  rw [Nat.testBit_xor, Nat.testBit_xor, hb1] at hzero
  have hone : (pair a2 b2).testBit a1 = true ∨ (pair a3 b3).testBit a1 = true := by
    by_contra hc
    push_neg at hc
    obtain ⟨k2, k3⟩ := hc
    have k2' : (pair a2 b2).testBit a1 = false := by
      cases hb : (pair a2 b2).testBit a1
      · rfl
      · exact absurd hb k2
    have k3' : (pair a3 b3).testBit a1 = false := by
      cases hb : (pair a3 b3).testBit a1
      · rfl
      · exact absurd hb k3
    rw [k2', k3'] at hzero
    simp at hzero
  -- P3 = P1 xor P2, and P2 = P1 xor P3
  have hP3 : pair a1 b1 ^^^ pair a2 b2 = pair a3 b3 := xor_eq_of_xor_eq_zero hxor
  have hP2 : pair a1 b1 ^^^ pair a3 b3 = pair a2 b2 := by
    rw [← hP3, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rcases hone with hin2 | hin3
  · -- a1 lies in the second pair; write it as `pair a1 r`
    obtain ⟨r, hr, hP2eq⟩ : ∃ r, a1 ≠ r ∧ pair a2 b2 = pair a1 r := by
      rcases mem_pair_iff.mp hin2 with he | he
      · exact ⟨b2, by rw [he]; exact h2, by rw [he]⟩
      · exact ⟨a2, by rw [he]; exact Ne.symm h2, by rw [he]; exact pair_comm a2 b2⟩
    have hb1r : b1 ≠ r := by
      rintro rfl
      exact d12 (by rw [hP2eq])
    refine ⟨a1, b1, r, h1, hr, hb1r, rfl, hP2eq, ?_⟩
    rw [← hP3, hP2eq, pair_xor_pair_left h1 hr hb1r]
  · -- a1 lies in the third pair; write it as `pair a1 r`
    obtain ⟨r, hr, hP3eq⟩ : ∃ r, a1 ≠ r ∧ pair a3 b3 = pair a1 r := by
      rcases mem_pair_iff.mp hin3 with he | he
      · exact ⟨b3, by rw [he]; exact h3, by rw [he]⟩
      · exact ⟨a3, by rw [he]; exact Ne.symm h3, by rw [he]; exact pair_comm a3 b3⟩
    have hb1r : b1 ≠ r := by
      rintro rfl
      exact d13 (by rw [hP3eq])
    refine ⟨b1, a1, r, Ne.symm h1, hb1r, hr, ?_, ?_, ?_⟩
    · exact pair_comm a1 b1
    · rw [← hP2, hP3eq, pair_xor_pair_left h1 hr hb1r]
    · rw [hP3eq]


/-! ## `LinkType` is symmetric in the four sets

The classification proof normalises (e.g. "the set that is empty comes first") and then
permutes back, exactly as `four_pairs_cycle` calls `cycle_aux1` with permuted arguments.
The three adjacent transpositions generate all of `S_4`.
-/

lemma linkType_swap12 {T1 T2 T3 T4 : ℕ} (h : LinkType T1 T2 T3 T4) :
    LinkType T2 T1 T3 T4 := by
  rcases h with ⟨p, q, r, s, e1, e2, e3, e4, e5, e6, g1, g2, g3, g4⟩ |
    ⟨a, b, hab, g1, g2, g3, g4⟩ | ⟨a, b, c, k1, k2, k3, g1, g2, g3, g4⟩ |
    ⟨a, b, c, k1, k2, k3, g1, g2, g3, g4⟩
  · exact Or.inl ⟨p, q, r, s, e1, e2, e3, e4, e5, e6, g2, g1, g3, g4⟩
  · exact Or.inr (Or.inl ⟨a, b, hab, g2, g1, g3, g4⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a, b, c, k1, k2, k3, g2, g1, g3, g4⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a, b, c, k1, k2, k3, g2, g1, g3, g4⟩))

lemma linkType_swap23 {T1 T2 T3 T4 : ℕ} (h : LinkType T1 T2 T3 T4) :
    LinkType T1 T3 T2 T4 := by
  rcases h with ⟨p, q, r, s, e1, e2, e3, e4, e5, e6, g1, g2, g3, g4⟩ |
    ⟨a, b, hab, g1, g2, g3, g4⟩ | ⟨a, b, c, k1, k2, k3, g1, g2, g3, g4⟩ |
    ⟨a, b, c, k1, k2, k3, g1, g2, g3, g4⟩
  · exact Or.inl ⟨p, q, r, s, e1, e2, e3, e4, e5, e6, g1, g3, g2, g4⟩
  · exact Or.inr (Or.inl ⟨a, b, hab, g1, g3, g2, g4⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a, b, c, k1, k2, k3, g1, g3, g2, g4⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a, b, c, k1, k2, k3, g1, g3, g2, g4⟩))

lemma linkType_swap34 {T1 T2 T3 T4 : ℕ} (h : LinkType T1 T2 T3 T4) :
    LinkType T1 T2 T4 T3 := by
  rcases h with ⟨p, q, r, s, e1, e2, e3, e4, e5, e6, g1, g2, g3, g4⟩ |
    ⟨a, b, hab, g1, g2, g3, g4⟩ | ⟨a, b, c, k1, k2, k3, g1, g2, g3, g4⟩ |
    ⟨a, b, c, k1, k2, k3, g1, g2, g3, g4⟩
  · exact Or.inl ⟨p, q, r, s, e1, e2, e3, e4, e5, e6, g1, g2, g4, g3⟩
  · exact Or.inr (Or.inl ⟨a, b, hab, g1, g2, g4, g3⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a, b, c, k1, k2, k3, g1, g2, g4, g3⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a, b, c, k1, k2, k3, g1, g2, g4, g3⟩))

/-- move the first set to the third slot: `T1 T2 T3 T4 → T2 T3 T1 T4` -/
lemma linkType_rot13 {T1 T2 T3 T4 : ℕ} (h : LinkType T1 T2 T3 T4) :
    LinkType T2 T3 T1 T4 :=
  linkType_swap23 (linkType_swap12 h)

/-- move the first set to the fourth slot: `T1 T2 T3 T4 → T2 T3 T4 T1` -/
lemma linkType_rot14 {T1 T2 T3 T4 : ℕ} (h : LinkType T1 T2 T3 T4) :
    LinkType T2 T3 T4 T1 :=
  linkType_swap34 (linkType_rot13 h)


/-! ## Small impossibility facts used by the case analysis -/

lemma pair_ne_zero {r s : ℕ} : pair r s ≠ 0 := by
  intro h
  have hr : (pair r s).testBit r = true := mem_pair_iff.mpr (Or.inl rfl)
  rw [h, Nat.zero_testBit] at hr
  exact Bool.noConfusion hr

/-- a pair is never a singleton -/
lemma pair_ne_two_pow {r s x : ℕ} (hrs : r ≠ s) : pair r s ≠ 2 ^ x := by
  intro h
  have hr : (pair r s).testBit r = true := mem_pair_iff.mpr (Or.inl rfl)
  have hs : (pair r s).testBit s = true := mem_pair_iff.mpr (Or.inr rfl)
  rw [h, Nat.testBit_two_pow] at hr hs
  simp only [decide_eq_true_eq] at hr hs
  exact hrs (hr.symm.trans hs)

/-- two distinct singletons xor to their pair -/
lemma two_pow_xor_two_pow {a b : ℕ} (hab : a ≠ b) : 2 ^ a ^^^ 2 ^ b = pair a b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_two_pow, testBit_pair]
  by_cases h1 : a = j <;> by_cases h2 : b = j <;> simp [h1, h2] <;> omega

/-- **the xor of two pairs is never a singleton** (the parity fact that rules out the
`s = 1` and `(0, singleton, pair, pair)` shapes) -/
lemma pair_xor_pair_ne_two_pow {p q r s x : ℕ} (hpq : p ≠ q) (hrs : r ≠ s) :
    pair p q ^^^ pair r s ≠ 2 ^ x := by
  intro h
  have hsplit : pair p q = pair r s ^^^ 2 ^ x := by
    have hc := congrArg (fun z => z ^^^ pair r s) h
    simp only at hc
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at hc
    rw [hc, Nat.xor_comm]
  by_cases hxr : x = r
  · rw [hxr, pair_xor_two_pow_left hrs] at hsplit
    exact pair_ne_two_pow hpq hsplit
  by_cases hxs : x = s
  · rw [hxs, pair_comm r s, pair_xor_two_pow_left (Ne.symm hrs)] at hsplit
    exact pair_ne_two_pow hpq hsplit
  · rw [pair_xor_two_pow (fun hc => hxr hc.symm) (fun hc => hxs hc.symm)] at hsplit
    have mx : x = p ∨ x = q := mem_pair_iff.mp (by rw [hsplit]; exact mem_tri_iff.mpr (Or.inl rfl))
    have mr : r = p ∨ r = q :=
      mem_pair_iff.mp (by rw [hsplit]; exact mem_tri_iff.mpr (Or.inr (Or.inl rfl)))
    have ms : s = p ∨ s = q :=
      mem_pair_iff.mp (by rw [hsplit]; exact mem_tri_iff.mpr (Or.inr (Or.inr rfl)))
    clear * - mx mr ms hrs hxr hxs
    omega

/-- three distinct singletons do not xor to zero -/
lemma three_two_pow_xor_ne_zero {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) :
    2 ^ a ^^^ 2 ^ b ^^^ 2 ^ c ≠ 0 := by
  intro h
  have key : (2 ^ a ^^^ 2 ^ b ^^^ 2 ^ c).testBit a = true := by
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_two_pow,
      Nat.testBit_two_pow]
    have e1 : decide (a = a) = true := by simp
    have e2 : decide (b = a) = false := by simp [Ne.symm hab]
    have e3 : decide (c = a) = false := by simp [Ne.symm hac]
    rw [e1, e2, e3]
    rfl
  rw [h, Nat.zero_testBit] at key
  exact Bool.noConfusion key

/-! ## xor of three terms is symmetric -/

lemma xor3_swap12 (A B C : ℕ) : A ^^^ B ^^^ C = B ^^^ A ^^^ C := by
  rw [Nat.xor_comm A B]

lemma xor3_swap23 (A B C : ℕ) : A ^^^ B ^^^ C = A ^^^ C ^^^ B := by
  rw [Nat.xor_assoc, Nat.xor_comm B C, ← Nat.xor_assoc]

lemma xor3_rot (A B C : ℕ) : A ^^^ B ^^^ C = B ^^^ C ^^^ A := by
  rw [Nat.xor_assoc, Nat.xor_comm A (B ^^^ C)]

/-! ## the three canonical shapes when one of the four sets is empty -/

lemma card_le_two_cases_ne_zero {n T : ℕ} (hT : T < 2 ^ n) (h2 : card n T ≤ 2) (hz : T ≠ 0) :
    (∃ a, a < n ∧ T = 2 ^ a) ∨ (∃ a b, a < n ∧ b < n ∧ a ≠ b ∧ T = pair a b) := by
  rcases card_le_two_cases hT h2 with h | h | h
  · exact absurd h hz
  · exact Or.inl h
  · exact Or.inr h

/-- two singletons among the three nonzero sets force the fourth to be their pair: **L2**. -/
lemma linkType_zero_two_singletons {a b T4 : ℕ} (hne : (2 : ℕ) ^ a ≠ 2 ^ b)
    (hxor : 2 ^ a ^^^ 2 ^ b ^^^ T4 = 0) : LinkType 0 (2 ^ a) (2 ^ b) T4 := by
  have hab : a ≠ b := by rintro rfl; exact hne rfl
  have hT4 : T4 = pair a b := by
    have hx := xor_eq_of_xor_eq_zero hxor
    rw [← hx, two_pow_xor_two_pow hab]
  exact Or.inr (Or.inl ⟨a, b, hab, Or.inl rfl, Or.inr (Or.inl rfl),
    Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inr (Or.inr hT4))⟩)

/-- exactly one singleton among the three nonzero sets is impossible: two pairs would have to
xor to a singleton. -/
lemma linkType_zero_one_singleton {a p q r s : ℕ} (hpq : p ≠ q) (hrs : r ≠ s)
    (hxor : 2 ^ a ^^^ pair p q ^^^ pair r s = 0) : False := by
  have h1 : 2 ^ a ^^^ pair p q = pair r s := xor_eq_of_xor_eq_zero hxor
  have h2 : pair p q ^^^ pair r s = 2 ^ a := by
    rw [← h1, ← Nat.xor_assoc, Nat.xor_comm (pair p q) (2 ^ a), Nat.xor_assoc,
      Nat.xor_self, Nat.xor_zero]
  exact pair_xor_pair_ne_two_pow hpq hrs h2

/-- three pairs among the three nonzero sets form a triangle: **L4**. -/
lemma linkType_zero_three_pairs {p q r s t u : ℕ} (hpq : p ≠ q) (hrs : r ≠ s) (htu : t ≠ u)
    (d23 : pair p q ≠ pair r s) (d24 : pair p q ≠ pair t u)
    (hxor : pair p q ^^^ pair r s ^^^ pair t u = 0) :
    LinkType 0 (pair p q) (pair r s) (pair t u) := by
  obtain ⟨x, y, z, hxy, hxz, hyz, e1, e2, e3⟩ :=
    three_pairs_triangle hpq hrs htu d23 d24 hxor
  exact Or.inr (Or.inr (Or.inr ⟨x, y, z, hxy, hxz, hyz, Or.inl rfl,
    Or.inr (Or.inl e1), Or.inr (Or.inr (Or.inr e2)), Or.inr (Or.inr (Or.inl e3))⟩))

/-- **The classification when one of the four sets is empty.** -/
lemma linkType_zero {n T2 T3 T4 : ℕ}
    (h2 : T2 < 2 ^ n) (h3 : T3 < 2 ^ n) (h4 : T4 < 2 ^ n)
    (c2 : card n T2 ≤ 2) (c3 : card n T3 ≤ 2) (c4 : card n T4 ≤ 2)
    (z2 : T2 ≠ 0) (z3 : T3 ≠ 0) (z4 : T4 ≠ 0)
    (d23 : T2 ≠ T3) (d24 : T2 ≠ T4) (d34 : T3 ≠ T4)
    (hxor : T2 ^^^ T3 ^^^ T4 = 0) : LinkType 0 T2 T3 T4 := by
  rcases card_le_two_cases_ne_zero h2 c2 z2 with ⟨a, -, rfl⟩ | ⟨p, q, -, -, hpq, rfl⟩
  · rcases card_le_two_cases_ne_zero h3 c3 z3 with ⟨b, -, rfl⟩ | ⟨r, s, -, -, hrs, rfl⟩
    · -- (S, S, ?)
      exact linkType_zero_two_singletons d23 hxor
    · rcases card_le_two_cases_ne_zero h4 c4 z4 with ⟨c, -, rfl⟩ | ⟨t, u, -, -, htu, rfl⟩
      · -- (S, P, S): put the two singletons in slots 2 and 3
        refine linkType_swap34 (linkType_zero_two_singletons d24 ?_)
        rw [← xor3_swap23]; exact hxor
      · -- (S, P, P): impossible
        exact (linkType_zero_one_singleton hrs htu hxor).elim
  · rcases card_le_two_cases_ne_zero h3 c3 z3 with ⟨b, -, rfl⟩ | ⟨r, s, -, -, hrs, rfl⟩
    · rcases card_le_two_cases_ne_zero h4 c4 z4 with ⟨c, -, rfl⟩ | ⟨t, u, -, -, htu, rfl⟩
      · -- (P, S, S)
        refine linkType_swap23 (linkType_swap34 (linkType_zero_two_singletons d34 ?_))
        rw [← xor3_rot]; exact hxor
      · -- (P, S, P): impossible
        refine (linkType_zero_one_singleton (a := b) hpq htu ?_).elim
        rw [← xor3_swap12]; exact hxor
    · rcases card_le_two_cases_ne_zero h4 c4 z4 with ⟨c, -, rfl⟩ | ⟨t, u, -, -, htu, rfl⟩
      · -- (P, P, S): impossible
        refine (linkType_zero_one_singleton (a := c) hpq hrs ?_).elim
        rw [← xor3_rot, ← xor3_rot]; exact hxor
      · -- (P, P, P)
        exact linkType_zero_three_pairs hpq hrs htu d23 d24 hxor


/-! ## Parity of cardinalities under xor

`card n (A ^^^ B ^^^ C ^^^ D) + |A| + |B| + |C| + |D|` is always even, because at each bit
the five indicators contribute 0 or 2.  With `A ^^^ B ^^^ C ^^^ D = 0` this says the four
sizes sum to an even number, which is what rules out every "odd number of singletons"
shape in one line.
-/

lemma card_eq_sum (n T : ℕ) : card n T = ∑ i ∈ range n, if T.testBit i then 1 else 0 := by
  unfold card
  rw [card_filter]

lemma card_zero_eq_zero (n : ℕ) : card n 0 = 0 := by
  rw [card_eq_sum]
  apply sum_eq_zero
  intro i _
  rw [Nat.zero_testBit]
  rfl

lemma card_xor_four_parity (n A B C D : ℕ) :
    2 ∣ (card n (A ^^^ B ^^^ C ^^^ D) + card n A + card n B + card n C + card n D) := by
  rw [card_eq_sum, card_eq_sum, card_eq_sum, card_eq_sum, card_eq_sum,
    ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  apply dvd_sum
  intro i _
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
  cases A.testBit i <;> cases B.testBit i <;> cases C.testBit i <;> cases D.testBit i <;>
    norm_num

/-- with xor 0 the four sizes sum to an even number -/
lemma card_sum_even {n A B C D : ℕ} (hxor : A ^^^ B ^^^ C ^^^ D = 0) :
    2 ∣ (card n A + card n B + card n C + card n D) := by
  have h := card_xor_four_parity n A B C D
  rw [hxor, card_zero_eq_zero, Nat.zero_add] at h
  exact h

/-! ## the canonical shapes when none of the four sets is empty -/

/-- four pairs: **L1**, the 4-cycle. -/
lemma linkType_four_pairs {a1 b1 a2 b2 a3 b3 a4 b4 : ℕ}
    (h1 : a1 ≠ b1) (h2 : a2 ≠ b2) (h3 : a3 ≠ b3) (h4 : a4 ≠ b4)
    (d12 : pair a1 b1 ≠ pair a2 b2) (d13 : pair a1 b1 ≠ pair a3 b3)
    (d14 : pair a1 b1 ≠ pair a4 b4) (d23 : pair a2 b2 ≠ pair a3 b3)
    (d24 : pair a2 b2 ≠ pair a4 b4) (d34 : pair a3 b3 ≠ pair a4 b4)
    (hxor : pair a1 b1 ^^^ pair a2 b2 ^^^ pair a3 b3 ^^^ pair a4 b4 = 0) :
    LinkType (pair a1 b1) (pair a2 b2) (pair a3 b3) (pair a4 b4) := by
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, c1, c2, c3, c4⟩ :=
    four_pairs_cycle h1 h2 h3 h4 d12 d13 d14 d23 d24 d34 hxor
  exact Or.inl ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, c1, c2, c3, c4⟩

/-- two singletons and two pairs: **L3**. -/
lemma linkType_two_singletons_two_pairs {a b p q r s : ℕ}
    (hne : (2 : ℕ) ^ a ≠ 2 ^ b) (hpq : p ≠ q) (hrs : r ≠ s)
    (hxor : 2 ^ a ^^^ 2 ^ b ^^^ pair p q ^^^ pair r s = 0) :
    LinkType (2 ^ a) (2 ^ b) (pair p q) (pair r s) := by
  have hab : a ≠ b := by rintro rfl; exact hne rfl
  have key : pair a b ^^^ pair p q ^^^ pair r s = 0 := by
    rw [← two_pow_xor_two_pow hab]; exact hxor
  have dab_pq : pair a b ≠ pair p q := by
    intro hc
    rw [hc, Nat.xor_self, Nat.zero_xor] at key
    exact pair_ne_zero key
  have dab_rs : pair a b ≠ pair r s := by
    intro hc
    rw [xor3_swap23] at key
    rw [hc, Nat.xor_self, Nat.zero_xor] at key
    exact pair_ne_zero key
  obtain ⟨x, y, z, hxy, hxz, hyz, e1, e2, e3⟩ :=
    three_pairs_triangle hab hpq hrs dab_pq dab_rs key
  rcases pair_eq_iff.mp e1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨a, b, z, hab, hxz, hyz, Or.inl rfl, Or.inr (Or.inl rfl),
      Or.inr (Or.inr (Or.inl e2)), Or.inr (Or.inr (Or.inr e3))⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨a, b, z, hab, hyz, hxz, Or.inl rfl, Or.inr (Or.inl rfl),
      Or.inr (Or.inr (Or.inr e2)), Or.inr (Or.inr (Or.inl e3))⟩))


/-! ## sizes of singletons and pairs -/

lemma card_two_pow {n a : ℕ} (ha : a < n) : card n (2 ^ a) = 1 := by
  unfold card
  have hf : (range n).filter (fun i => (2 ^ a).testBit i) = {a} := by
    ext i
    simp only [mem_filter, mem_range, mem_singleton, Nat.testBit_two_pow, decide_eq_true_eq]
    constructor
    · rintro ⟨-, rfl⟩; rfl
    · rintro rfl; exact ⟨ha, rfl⟩
  rw [hf, card_singleton]

lemma card_pair_eq {n p q : ℕ} (hp : p < n) (hq : q < n) (hpq : p ≠ q) :
    card n (pair p q) = 2 := by
  unfold card
  have hf : (range n).filter (fun i => (pair p q).testBit i) = {p, q} := by
    ext i
    simp only [mem_filter, mem_range, mem_insert, mem_singleton, testBit_pair,
      Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨-, h | h⟩
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (rfl | rfl)
      · exact ⟨hp, Or.inl rfl⟩
      · exact ⟨hq, Or.inr rfl⟩
  rw [hf, card_pair hpq]

/-- four distinct singletons do not xor to zero -/
lemma four_two_pow_xor_ne_zero {a b c d : ℕ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    2 ^ a ^^^ 2 ^ b ^^^ 2 ^ c ^^^ 2 ^ d ≠ 0 := by
  intro h
  have key : (2 ^ a ^^^ 2 ^ b ^^^ 2 ^ c ^^^ 2 ^ d).testBit a = true := by
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_two_pow,
      Nat.testBit_two_pow, Nat.testBit_two_pow, Nat.testBit_two_pow]
    have e1 : decide (a = a) = true := by simp
    have e2 : decide (b = a) = false := by simp [Ne.symm hab]
    have e3 : decide (c = a) = false := by simp [Ne.symm hac]
    have e4 : decide (d = a) = false := by simp [Ne.symm had]
    rw [e1, e2, e3, e4]
    rfl
  rw [h, Nat.zero_testBit] at key
  exact Bool.noConfusion key

/-- **The classification when none of the four sets is empty.** -/
lemma linkType_nozero {n T1 T2 T3 T4 : ℕ}
    (b1 : T1 < 2 ^ n) (b2 : T2 < 2 ^ n) (b3 : T3 < 2 ^ n) (b4 : T4 < 2 ^ n)
    (c1 : card n T1 ≤ 2) (c2 : card n T2 ≤ 2) (c3 : card n T3 ≤ 2) (c4 : card n T4 ≤ 2)
    (z1 : T1 ≠ 0) (z2 : T2 ≠ 0) (z3 : T3 ≠ 0) (z4 : T4 ≠ 0)
    (d12 : T1 ≠ T2) (d13 : T1 ≠ T3) (d14 : T1 ≠ T4)
    (d23 : T2 ≠ T3) (d24 : T2 ≠ T4) (d34 : T3 ≠ T4)
    (hxor : T1 ^^^ T2 ^^^ T3 ^^^ T4 = 0) : LinkType T1 T2 T3 T4 := by
  rcases card_le_two_cases_ne_zero b1 c1 z1 with ⟨a1, ha1, rfl⟩ | ⟨p1, q1, hp1, hq1, hpq1, rfl⟩
  · rcases card_le_two_cases_ne_zero b2 c2 z2 with ⟨a2, ha2, rfl⟩ | ⟨p2, q2, hp2, hq2, hpq2, rfl⟩
    · rcases card_le_two_cases_ne_zero b3 c3 z3 with ⟨a3, ha3, rfl⟩ | ⟨p3, q3, hp3, hq3, hpq3, rfl⟩
      · rcases card_le_two_cases_ne_zero b4 c4 z4 with ⟨a4, ha4, rfl⟩ | ⟨p4, q4, hp4, hq4, hpq4, rfl⟩
        · -- four singletons: impossible
          exact absurd hxor (four_two_pow_xor_ne_zero (fun h => d12 (by rw [h]))
            (fun h => d13 (by rw [h])) (fun h => d14 (by rw [h])))
        · -- an odd number of singletons: the four sizes would sum to an odd number
          exfalso
          have hpar := card_sum_even (n := n) hxor
          rw [card_two_pow ha1, card_two_pow ha2, card_two_pow ha3, card_pair_eq hp4 hq4 hpq4] at hpar
          omega
      · rcases card_le_two_cases_ne_zero b4 c4 z4 with ⟨a4, ha4, rfl⟩ | ⟨p4, q4, hp4, hq4, hpq4, rfl⟩
        · -- an odd number of singletons: the four sizes would sum to an odd number
          exfalso
          have hpar := card_sum_even (n := n) hxor
          rw [card_two_pow ha1, card_two_pow ha2, card_pair_eq hp3 hq3 hpq3, card_two_pow ha4] at hpar
          omega
        · -- two singletons (slots 1, 2) and two pairs
          have hx' : 2 ^ a1 ^^^ 2 ^ a2 ^^^ pair p3 q3 ^^^ pair p4 q4 = 0 := by
            rw [← hxor]
            try ac_rfl
          exact linkType_two_singletons_two_pairs d12 hpq3 hpq4 hx'
    · rcases card_le_two_cases_ne_zero b3 c3 z3 with ⟨a3, ha3, rfl⟩ | ⟨p3, q3, hp3, hq3, hpq3, rfl⟩
      · rcases card_le_two_cases_ne_zero b4 c4 z4 with ⟨a4, ha4, rfl⟩ | ⟨p4, q4, hp4, hq4, hpq4, rfl⟩
        · -- an odd number of singletons: the four sizes would sum to an odd number
          exfalso
          have hpar := card_sum_even (n := n) hxor
          rw [card_two_pow ha1, card_pair_eq hp2 hq2 hpq2, card_two_pow ha3, card_two_pow ha4] at hpar
          omega
        · -- two singletons (slots 1, 3) and two pairs
          have hx' : 2 ^ a1 ^^^ 2 ^ a3 ^^^ pair p2 q2 ^^^ pair p4 q4 = 0 := by
            rw [← hxor]
            try ac_rfl
          exact linkType_swap23 (linkType_two_singletons_two_pairs d13 hpq2 hpq4 hx')
      · rcases card_le_two_cases_ne_zero b4 c4 z4 with ⟨a4, ha4, rfl⟩ | ⟨p4, q4, hp4, hq4, hpq4, rfl⟩
        · -- two singletons (slots 1, 4) and two pairs
          have hx' : 2 ^ a1 ^^^ 2 ^ a4 ^^^ pair p2 q2 ^^^ pair p3 q3 = 0 := by
            rw [← hxor]
            try ac_rfl
          exact linkType_swap34 (linkType_swap23 (linkType_two_singletons_two_pairs d14 hpq2 hpq3 hx'))
        · -- an odd number of singletons: the four sizes would sum to an odd number
          exfalso
          have hpar := card_sum_even (n := n) hxor
          rw [card_two_pow ha1, card_pair_eq hp2 hq2 hpq2, card_pair_eq hp3 hq3 hpq3, card_pair_eq hp4 hq4 hpq4] at hpar
          omega
  · rcases card_le_two_cases_ne_zero b2 c2 z2 with ⟨a2, ha2, rfl⟩ | ⟨p2, q2, hp2, hq2, hpq2, rfl⟩
    · rcases card_le_two_cases_ne_zero b3 c3 z3 with ⟨a3, ha3, rfl⟩ | ⟨p3, q3, hp3, hq3, hpq3, rfl⟩
      · rcases card_le_two_cases_ne_zero b4 c4 z4 with ⟨a4, ha4, rfl⟩ | ⟨p4, q4, hp4, hq4, hpq4, rfl⟩
        · -- an odd number of singletons: the four sizes would sum to an odd number
          exfalso
          have hpar := card_sum_even (n := n) hxor
          rw [card_pair_eq hp1 hq1 hpq1, card_two_pow ha2, card_two_pow ha3, card_two_pow ha4] at hpar
          omega
        · -- two singletons (slots 2, 3) and two pairs
          have hx' : 2 ^ a2 ^^^ 2 ^ a3 ^^^ pair p1 q1 ^^^ pair p4 q4 = 0 := by
            rw [← hxor]
            try ac_rfl
          exact linkType_rot13 (linkType_rot13 (linkType_two_singletons_two_pairs d23 hpq1 hpq4 hx'))
      · rcases card_le_two_cases_ne_zero b4 c4 z4 with ⟨a4, ha4, rfl⟩ | ⟨p4, q4, hp4, hq4, hpq4, rfl⟩
        · -- two singletons (slots 2, 4) and two pairs
          have hx' : 2 ^ a2 ^^^ 2 ^ a4 ^^^ pair p1 q1 ^^^ pair p3 q3 = 0 := by
            rw [← hxor]
            try ac_rfl
          exact linkType_swap34 (linkType_swap12 (linkType_swap23 (linkType_two_singletons_two_pairs d24 hpq1 hpq3 hx')))
        · -- an odd number of singletons: the four sizes would sum to an odd number
          exfalso
          have hpar := card_sum_even (n := n) hxor
          rw [card_pair_eq hp1 hq1 hpq1, card_two_pow ha2, card_pair_eq hp3 hq3 hpq3, card_pair_eq hp4 hq4 hpq4] at hpar
          omega
    · rcases card_le_two_cases_ne_zero b3 c3 z3 with ⟨a3, ha3, rfl⟩ | ⟨p3, q3, hp3, hq3, hpq3, rfl⟩
      · rcases card_le_two_cases_ne_zero b4 c4 z4 with ⟨a4, ha4, rfl⟩ | ⟨p4, q4, hp4, hq4, hpq4, rfl⟩
        · -- two singletons (slots 3, 4) and two pairs
          have hx' : 2 ^ a3 ^^^ 2 ^ a4 ^^^ pair p1 q1 ^^^ pair p2 q2 = 0 := by
            rw [← hxor]
            try ac_rfl
          exact linkType_swap23 (linkType_swap34 (linkType_swap12 (linkType_swap23 (linkType_two_singletons_two_pairs d34 hpq1 hpq2 hx'))))
        · -- an odd number of singletons: the four sizes would sum to an odd number
          exfalso
          have hpar := card_sum_even (n := n) hxor
          rw [card_pair_eq hp1 hq1 hpq1, card_pair_eq hp2 hq2 hpq2, card_two_pow ha3, card_pair_eq hp4 hq4 hpq4] at hpar
          omega
      · rcases card_le_two_cases_ne_zero b4 c4 z4 with ⟨a4, ha4, rfl⟩ | ⟨p4, q4, hp4, hq4, hpq4, rfl⟩
        · -- an odd number of singletons: the four sizes would sum to an odd number
          exfalso
          have hpar := card_sum_even (n := n) hxor
          rw [card_pair_eq hp1 hq1 hpq1, card_pair_eq hp2 hq2 hpq2, card_pair_eq hp3 hq3 hpq3, card_two_pow ha4] at hpar
          omega
        · -- four pairs: the 4-cycle
          exact linkType_four_pairs hpq1 hpq2 hpq3 hpq4 d12 d13 d14 d23 d24 d34 hxor

/-- **Lemma 2(a) of R3_equals_10.md: the L1..L4 classification.**  Four distinct subsets of
`[n]` of size at most two whose symmetric difference is empty form a 4-cycle of pairs (L1),
or `∅, {a}, {b}, {a,b}` (L2), or `{a}, {b}, {a,c}, {b,c}` (L3), or `∅, {a,b}, {b,c}, {a,c}`
(L4). -/
theorem link_types {n T1 T2 T3 T4 : ℕ}
    (b1 : T1 < 2 ^ n) (b2 : T2 < 2 ^ n) (b3 : T3 < 2 ^ n) (b4 : T4 < 2 ^ n)
    (c1 : card n T1 ≤ 2) (c2 : card n T2 ≤ 2) (c3 : card n T3 ≤ 2) (c4 : card n T4 ≤ 2)
    (d12 : T1 ≠ T2) (d13 : T1 ≠ T3) (d14 : T1 ≠ T4)
    (d23 : T2 ≠ T3) (d24 : T2 ≠ T4) (d34 : T3 ≠ T4)
    (hxor : T1 ^^^ T2 ^^^ T3 ^^^ T4 = 0) : LinkType T1 T2 T3 T4 := by
  by_cases z1 : T1 = 0
  · subst z1
    rw [Nat.zero_xor] at hxor
    exact linkType_zero b2 b3 b4 c2 c3 c4 (Ne.symm d12) (Ne.symm d13) (Ne.symm d14)
      d23 d24 d34 hxor
  by_cases z2 : T2 = 0
  · subst z2
    rw [Nat.xor_zero] at hxor
    exact linkType_swap12 (linkType_zero b1 b3 b4 c1 c3 c4 z1 (Ne.symm d23) (Ne.symm d24)
      d13 d14 d34 hxor)
  by_cases z3 : T3 = 0
  · subst z3
    rw [Nat.xor_zero] at hxor
    exact linkType_rot13 (linkType_zero b1 b2 b4 c1 c2 c4 z1 z2 (Ne.symm d34)
      d12 d14 d24 hxor)
  by_cases z4 : T4 = 0
  · subst z4
    rw [Nat.xor_zero] at hxor
    exact linkType_rot14 (linkType_zero b1 b2 b3 c1 c2 c3 z1 z2 z3 d12 d13 d23 hxor)
  · exact linkType_nozero b1 b2 b3 b4 c1 c2 c3 c4 z1 z2 z3 z4 d12 d13 d14 d23 d24 d34 hxor

end R3
