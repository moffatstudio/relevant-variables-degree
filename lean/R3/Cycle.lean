import R3.Twelve
/-!
# Four distinct pairs with empty symmetric difference form a 4-cycle

Step 2 of R3_upper_bound.md (the link shape at a vertex all of whose terms are cubic):
if `T₁,…,T₄` are four distinct 2-element subsets with `T₁ Δ T₂ Δ T₃ Δ T₄ = ∅`, then there are
four distinct vertices `p,q,r,s` with `{T_i} = {pq, qr, rs, sp}`  (`four_pairs_cycle`).
Applied to a 12-variable solution: every vertex link is a 4-cycle (`twelve_link_cycle`).

Pairs are bitmasks `pair p q = 2^p ||| 2^q`.
-/
namespace R3
open Finset

/-- bitmask of the pair {p, q} -/
def pair (p q : ℕ) : ℕ := 2 ^ p ||| 2 ^ q

lemma pair_comm (p q : ℕ) : pair p q = pair q p := Nat.lor_comm _ _

lemma testBit_pair (p q j : ℕ) :
    (pair p q).testBit j = (decide (p = j) || decide (q = j)) := by
  simp [pair, Nat.testBit_or, Nat.testBit_two_pow]

lemma mem_pair_iff {p q j : ℕ} : (pair p q).testBit j = true ↔ j = p ∨ j = q := by
  rw [testBit_pair]; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega

lemma pair_eq_iff {a b c d : ℕ} :
    pair a b = pair c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha : a = c ∨ a = d := mem_pair_iff.mp (by rw [← h]; exact mem_pair_iff.mpr (Or.inl rfl))
    have hb : b = c ∨ b = d := mem_pair_iff.mp (by rw [← h]; exact mem_pair_iff.mpr (Or.inr rfl))
    have hc : c = a ∨ c = b := mem_pair_iff.mp (by rw [h]; exact mem_pair_iff.mpr (Or.inl rfl))
    have hd : d = a ∨ d = b := mem_pair_iff.mp (by rw [h]; exact mem_pair_iff.mpr (Or.inr rfl))
    omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact pair_comm _ _

/-- a bitmask below `2^n` with exactly two bits (below `n`) is a pair -/
lemma exists_pair_of_card_two {n T : ℕ} (hT : T < 2 ^ n) (h2 : card n T = 2) :
    ∃ p q, p < n ∧ q < n ∧ p ≠ q ∧ T = pair p q := by
  unfold card at h2
  obtain ⟨p, q, hpq, hf⟩ := card_eq_two.mp h2
  have hmem : ∀ j, T.testBit j = true ↔ j = p ∨ j = q := by
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
  have hp : p < n := by
    have : p ∈ (range n).filter (fun i => T.testBit i) := by rw [hf]; simp
    exact mem_range.mp (mem_filter.mp this).1
  have hq : q < n := by
    have : q ∈ (range n).filter (fun i => T.testBit i) := by rw [hf]; simp
    exact mem_range.mp (mem_filter.mp this).1
  refine ⟨p, q, hp, hq, hpq, ?_⟩
  apply Nat.eq_of_testBit_eq; intro j
  rw [Bool.eq_iff_iff, hmem j, mem_pair_iff]

/-! ## Degree counting -/

/-- number of times `j` occurs in the pair (a, b) -/
def cnt (a b j : ℕ) : ℕ := (if a = j then 1 else 0) + (if b = j then 1 else 0)

lemma cnt_eq {a b j : ℕ} (h : a ≠ b) : cnt a b j = if a = j ∨ b = j then 1 else 0 := by
  unfold cnt; split_ifs <;> omega

lemma cnt_comm (a b j : ℕ) : cnt a b j = cnt b a j := by
  unfold cnt; omega

lemma cnt_zero {a b j : ℕ} (ha : a ≠ j) (hb : b ≠ j) : cnt a b j = 0 := by
  unfold cnt; rw [if_neg ha, if_neg hb]

lemma cnt_one {a b j : ℕ} (h : a ≠ b) (hj : a = j ∨ b = j) : cnt a b j = 1 := by
  unfold cnt; split_ifs <;> omega

lemma cnt_cases (a b j : ℕ) :
    (cnt a b j = 0 ∧ a ≠ j ∧ b ≠ j) ∨ (cnt a b j = 1 ∧ (a = j ∨ b = j)) ∨
    (cnt a b j = 2 ∧ a = j ∧ b = j) := by
  unfold cnt; split_ifs <;> omega

/-- every vertex has even degree in the four pairs -/
def EvenDeg (a1 b1 a2 b2 a3 b3 a4 b4 : ℕ) : Prop := ∀ j,
    cnt a1 b1 j + cnt a2 b2 j + cnt a3 b3 j + cnt a4 b4 j = 0 ∨
    cnt a1 b1 j + cnt a2 b2 j + cnt a3 b3 j + cnt a4 b4 j = 2 ∨
    cnt a1 b1 j + cnt a2 b2 j + cnt a3 b3 j + cnt a4 b4 j = 4

/-- xor 0 ⇒ even degrees -/
lemma evenDeg_of_xor {a1 b1 a2 b2 a3 b3 a4 b4 : ℕ}
    (h1 : a1 ≠ b1) (h2 : a2 ≠ b2) (h3 : a3 ≠ b3) (h4 : a4 ≠ b4)
    (hxor : pair a1 b1 ^^^ pair a2 b2 ^^^ pair a3 b3 ^^^ pair a4 b4 = 0) :
    EvenDeg a1 b1 a2 b2 a3 b3 a4 b4 := by
  intro j
  have h := four_bool_even (testBit_xor_four (j := j) hxor)
  simp only [testBit_pair, Bool.or_eq_true, decide_eq_true_eq] at h
  rw [cnt_eq h1, cnt_eq h2, cnt_eq h3, cnt_eq h4]
  split_ifs at h ⊢ <;> omega

/-- `T` is an edge of the 4-cycle p-q-r-s-p -/
def OnCycle (p q r s T : ℕ) : Prop :=
  T = pair p q ∨ T = pair q r ∨ T = pair r s ∨ T = pair s p

lemma onCycle_comm {p q r s a b : ℕ} (h : OnCycle p q r s (pair a b)) :
    OnCycle p q r s (pair b a) := by
  rwa [pair_comm b a]

/-- the conclusion of the cycle lemma for the four pairs (a1,b1), (a2,b2), (a3,b3), (a4,b4) -/
def IsCycle (a1 b1 a2 b2 a3 b3 a4 b4 : ℕ) : Prop :=
  ∃ p q r s, p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
    OnCycle p q r s (pair a1 b1) ∧ OnCycle p q r s (pair a2 b2) ∧
    OnCycle p q r s (pair a3 b3) ∧ OnCycle p q r s (pair a4 b4)

/-- stage 2: T₁ = {a1,b1}, T₂ = {a1,r}, T₃ = {b1,s}, T₄ = {a4,b4} -/
lemma cycle_aux2 {a1 b1 r s a4 b4 : ℕ}
    (h1 : a1 ≠ b1) (hr1 : r ≠ a1) (hr2 : r ≠ b1) (hs1 : s ≠ a1) (hs2 : s ≠ b1) (h4 : a4 ≠ b4)
    (d34 : ¬((b1 = a4 ∧ s = b4) ∨ (b1 = b4 ∧ s = a4)))
    (D : EvenDeg a1 b1 a1 r b1 s a4 b4) :
    IsCycle a1 b1 a1 r b1 s a4 b4 := by
  by_cases hrs : r = s
  · exfalso
    subst s
    have Da4 := D a4
    have c1 := cnt_cases a1 b1 a4
    have c2 := cnt_cases a1 r a4
    have c3 := cnt_cases b1 r a4
    have c4 := cnt_one h4 (Or.inl rfl)
    clear * - Da4 c1 c2 c3 c4 h1 hr1 hr2
    omega
  · have hr4 : r = a4 ∨ r = b4 := by
      have Dr := D r
      have c1 := cnt_zero (a := a1) (b := b1) (j := r) hr1.symm hr2.symm
      have c2 := cnt_one (a := a1) (b := r) (j := r) hr1.symm (Or.inr rfl)
      have c3 := cnt_zero (a := b1) (b := s) (j := r) hr2.symm (fun h => hrs h.symm)
      have c4 := cnt_cases a4 b4 r
      clear * - Dr c1 c2 c3 c4
      omega
    have hs4 : s = a4 ∨ s = b4 := by
      have Ds := D s
      have c1 := cnt_zero (a := a1) (b := b1) (j := s) hs1.symm hs2.symm
      have c2 := cnt_zero (a := a1) (b := r) (j := s) hs1.symm hrs
      have c3 := cnt_one (a := b1) (b := s) (j := s) hs2.symm (Or.inr rfl)
      have c4 := cnt_cases a4 b4 s
      clear * - Ds c1 c2 c3 c4
      omega
    refine ⟨a1, b1, s, r, h1, hs1.symm, hr1.symm, hs2.symm, hr2.symm, fun h => hrs h.symm,
      ?_, ?_, ?_, ?_⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (pair_comm _ _)))
    · exact Or.inr (Or.inl rfl)
    · right; right; left
      rw [pair_eq_iff]
      clear * - hr4 hs4 hrs
      omega

/-- stage 1: T₁ = {a1,b1}, T₂ = {a1,r} -/
lemma cycle_aux1 {a1 b1 r a3 b3 a4 b4 : ℕ}
    (h1 : a1 ≠ b1) (hr : a1 ≠ r) (h3 : a3 ≠ b3) (h4 : a4 ≠ b4)
    (d12 : ¬((a1 = a1 ∧ b1 = r) ∨ (a1 = r ∧ b1 = a1)))
    (d13 : ¬((a1 = a3 ∧ b1 = b3) ∨ (a1 = b3 ∧ b1 = a3)))
    (d14 : ¬((a1 = a4 ∧ b1 = b4) ∨ (a1 = b4 ∧ b1 = a4)))
    (d23 : ¬((a1 = a3 ∧ r = b3) ∨ (a1 = b3 ∧ r = a3)))
    (d24 : ¬((a1 = a4 ∧ r = b4) ∨ (a1 = b4 ∧ r = a4)))
    (d34 : ¬((a3 = a4 ∧ b3 = b4) ∨ (a3 = b4 ∧ b3 = a4)))
    (D : EvenDeg a1 b1 a1 r a3 b3 a4 b4) :
    IsCycle a1 b1 a1 r a3 b3 a4 b4 := by
  have hrb : r ≠ b1 := fun h => d12 (Or.inl ⟨rfl, h.symm⟩)
  have hb1 : b1 = a3 ∨ b1 = b3 ∨ b1 = a4 ∨ b1 = b4 := by
    have Db := D b1
    have c1 := cnt_one (a := a1) (b := b1) (j := b1) h1 (Or.inr rfl)
    have c2 := cnt_zero (a := a1) (b := r) (j := b1) h1 hrb
    have c3 := cnt_cases a3 b3 b1
    have c4 := cnt_cases a4 b4 b1
    clear * - Db c1 c2 c3 c4
    omega
  rcases hb1 with h | h | h | h
  · -- T₃ = {b1, b3}
    subst a3
    exact cycle_aux2 h1 hr.symm hrb (by clear * - d13; omega) (fun h => h3 h.symm) h4
      (by clear * - d34; omega) D
  · -- T₃ = {a3, b1}
    subst b3
    obtain ⟨p, q, r', s', hpq, hpr, hps, hqr, hqs, hrs, c1, c2, c3, c4⟩ :=
      cycle_aux2 (a1 := a1) (b1 := b1) (r := r) (s := a3) (a4 := a4) (b4 := b4)
        h1 hr.symm hrb (by clear * - d13; omega) h3 h4 (by clear * - d34; omega)
        (fun j => by have := D j; rw [cnt_comm a3 b1] at this; clear * - this; omega)
    exact ⟨p, q, r', s', hpq, hpr, hps, hqr, hqs, hrs, c1, c2, onCycle_comm c3, c4⟩
  · -- T₄ = {b1, b4}
    subst a4
    obtain ⟨p, q, r', s', hpq, hpr, hps, hqr, hqs, hrs, c1, c2, c3, c4⟩ :=
      cycle_aux2 (a1 := a1) (b1 := b1) (r := r) (s := b4) (a4 := a3) (b4 := b3)
        h1 hr.symm hrb (by clear * - d14; omega) (fun h => h4 h.symm) h3
        (by clear * - d34; omega)
        (fun j => by have := D j; clear * - this; omega)
    exact ⟨p, q, r', s', hpq, hpr, hps, hqr, hqs, hrs, c1, c2, c4, c3⟩
  · -- T₄ = {a4, b1}
    subst b4
    obtain ⟨p, q, r', s', hpq, hpr, hps, hqr, hqs, hrs, c1, c2, c3, c4⟩ :=
      cycle_aux2 (a1 := a1) (b1 := b1) (r := r) (s := a4) (a4 := a3) (b4 := b3)
        h1 hr.symm hrb (by clear * - d14; omega) h4 h3 (by clear * - d34; omega)
        (fun j => by have := D j; rw [cnt_comm a4 b1] at this; clear * - this; omega)
    exact ⟨p, q, r', s', hpq, hpr, hps, hqr, hqs, hrs, c1, c2, c4, onCycle_comm c3⟩

/-- **Four distinct pairs with xor 0 form a 4-cycle.** -/
theorem four_pairs_cycle {a1 b1 a2 b2 a3 b3 a4 b4 : ℕ}
    (h1 : a1 ≠ b1) (h2 : a2 ≠ b2) (h3 : a3 ≠ b3) (h4 : a4 ≠ b4)
    (d12 : pair a1 b1 ≠ pair a2 b2) (d13 : pair a1 b1 ≠ pair a3 b3)
    (d14 : pair a1 b1 ≠ pair a4 b4) (d23 : pair a2 b2 ≠ pair a3 b3)
    (d24 : pair a2 b2 ≠ pair a4 b4) (d34 : pair a3 b3 ≠ pair a4 b4)
    (hxor : pair a1 b1 ^^^ pair a2 b2 ^^^ pair a3 b3 ^^^ pair a4 b4 = 0) :
    IsCycle a1 b1 a2 b2 a3 b3 a4 b4 := by
  have D := evenDeg_of_xor h1 h2 h3 h4 hxor
  rw [Ne, pair_eq_iff] at d12 d13 d14 d23 d24 d34
  have ha1 : a1 = a2 ∨ a1 = b2 ∨ a1 = a3 ∨ a1 = b3 ∨ a1 = a4 ∨ a1 = b4 := by
    have Da := D a1
    have c1 := cnt_one (a := a1) (b := b1) (j := a1) h1 (Or.inl rfl)
    have c2 := cnt_cases a2 b2 a1
    have c3 := cnt_cases a3 b3 a1
    have c4 := cnt_cases a4 b4 a1
    clear * - Da c1 c2 c3 c4
    omega
  rcases ha1 with h | h | h | h | h | h
  · -- T₂ = {a1, b2}
    subst a2
    exact cycle_aux1 h1 h2 h3 h4 d12 d13 d14 d23 d24 d34 D
  · -- T₂ = {a2, a1}
    subst b2
    obtain ⟨p, q, r', s', hpq, hpr, hps, hqr, hqs, hrs, c1, c2, c3, c4⟩ :=
      cycle_aux1 (a1 := a1) (b1 := b1) (r := a2) (a3 := a3) (b3 := b3) (a4 := a4) (b4 := b4)
        h1 (fun h => h2 h.symm) h3 h4
        (by clear * - d12; omega) (by clear * - d13; omega) (by clear * - d14; omega)
        (by clear * - d23; omega) (by clear * - d24; omega) (by clear * - d34; omega)
        (fun j => by have := D j; rw [cnt_comm a2 a1] at this; clear * - this; omega)
    exact ⟨p, q, r', s', hpq, hpr, hps, hqr, hqs, hrs, c1, onCycle_comm c2, c3, c4⟩
  · -- T₃ = {a1, b3}
    subst a3
    obtain ⟨p, q, r', s', hpq, hpr, hps, hqr, hqs, hrs, c1, c2, c3, c4⟩ :=
      cycle_aux1 (a1 := a1) (b1 := b1) (r := b3) (a3 := a2) (b3 := b2) (a4 := a4) (b4 := b4)
        h1 h3 h2 h4
        (by clear * - d13; omega) (by clear * - d12; omega) (by clear * - d14; omega)
        (by clear * - d23; omega) (by clear * - d34; omega) (by clear * - d24; omega)
        (fun j => by have := D j; clear * - this; omega)
    exact ⟨p, q, r', s', hpq, hpr, hps, hqr, hqs, hrs, c1, c3, c2, c4⟩
  · -- T₃ = {a3, a1}
    subst b3
    obtain ⟨p, q, r', s', hpq, hpr, hps, hqr, hqs, hrs, c1, c2, c3, c4⟩ :=
      cycle_aux1 (a1 := a1) (b1 := b1) (r := a3) (a3 := a2) (b3 := b2) (a4 := a4) (b4 := b4)
        h1 (fun h => h3 h.symm) h2 h4
        (by clear * - d13; omega) (by clear * - d12; omega) (by clear * - d14; omega)
        (by clear * - d23; omega) (by clear * - d34; omega) (by clear * - d24; omega)
        (fun j => by have := D j; rw [cnt_comm a3 a1] at this; clear * - this; omega)
    exact ⟨p, q, r', s', hpq, hpr, hps, hqr, hqs, hrs, c1, c3, onCycle_comm c2, c4⟩
  · -- T₄ = {a1, b4}
    subst a4
    obtain ⟨p, q, r', s', hpq, hpr, hps, hqr, hqs, hrs, c1, c2, c3, c4⟩ :=
      cycle_aux1 (a1 := a1) (b1 := b1) (r := b4) (a3 := a2) (b3 := b2) (a4 := a3) (b4 := b3)
        h1 h4 h2 h3
        (by clear * - d14; omega) (by clear * - d12; omega) (by clear * - d13; omega)
        (by clear * - d24; omega) (by clear * - d34; omega) (by clear * - d23; omega)
        (fun j => by have := D j; clear * - this; omega)
    exact ⟨p, q, r', s', hpq, hpr, hps, hqr, hqs, hrs, c1, c3, c4, c2⟩
  · -- T₄ = {a4, a1}
    subst b4
    obtain ⟨p, q, r', s', hpq, hpr, hps, hqr, hqs, hrs, c1, c2, c3, c4⟩ :=
      cycle_aux1 (a1 := a1) (b1 := b1) (r := a4) (a3 := a2) (b3 := b2) (a4 := a3) (b4 := b3)
        h1 (fun h => h4 h.symm) h2 h3
        (by clear * - d14; omega) (by clear * - d12; omega) (by clear * - d13; omega)
        (by clear * - d24; omega) (by clear * - d34; omega) (by clear * - d23; omega)
        (fun j => by have := D j; rw [cnt_comm a4 a1] at this; clear * - this; omega)
    exact ⟨p, q, r', s', hpq, hpr, hps, hqr, hqs, hrs, c1, c3, c4, onCycle_comm c2⟩

/-! ## Application: every link in a 12-variable solution is a 4-cycle -/

/-- n = 12: at every vertex `v` there are four distinct vertices `p,q,r,s` such that the
link set of every support set at `v` is an edge of the 4-cycle p-q-r-s-p. -/
theorem twelve_link_cycle {N : ℕ → ℤ} (hsol : IsSol 12 N) {v : ℕ} (hv : v < 12) :
    ∃ p q r s, p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
      ∀ S ∈ supp 12 N v, OnCycle p q r s (S ^^^ 2 ^ v) := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs, hall, hxor, -⟩ := twelve_link hsol hv
  have lt2 : ∀ S ∈ ({a, b, c, d} : Finset ℕ), S ^^^ 2 ^ v < 2 ^ 12 := by
    intro S hS
    exact Nat.xor_lt_two_pow (hall S hS).1 (Nat.pow_lt_pow_right (by norm_num) hv)
  obtain ⟨a1, b1, -, -, h1, e1⟩ := exists_pair_of_card_two (lt2 a (by simp)) (hall a (by simp)).2.2.2.2
  obtain ⟨a2, b2, -, -, h2, e2⟩ := exists_pair_of_card_two (lt2 b (by simp)) (hall b (by simp)).2.2.2.2
  obtain ⟨a3, b3, -, -, h3, e3⟩ := exists_pair_of_card_two (lt2 c (by simp)) (hall c (by simp)).2.2.2.2
  obtain ⟨a4, b4, -, -, h4, e4⟩ := exists_pair_of_card_two (lt2 d (by simp)) (hall d (by simp)).2.2.2.2
  have inj : ∀ x y : ℕ, x ^^^ 2 ^ v = y ^^^ 2 ^ v → x = y := by
    intro x y h
    have := congrArg (fun z => z ^^^ 2 ^ v) h
    simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this
  rw [e1, e2, e3, e4] at hxor
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, c1, c2, c3, c4⟩ :=
    four_pairs_cycle h1 h2 h3 h4
      (fun h => hab (inj _ _ (e1.trans (h.trans e2.symm))))
      (fun h => hac (inj _ _ (e1.trans (h.trans e3.symm))))
      (fun h => had (inj _ _ (e1.trans (h.trans e4.symm))))
      (fun h => hbc (inj _ _ (e2.trans (h.trans e3.symm))))
      (fun h => hbd (inj _ _ (e2.trans (h.trans e4.symm))))
      (fun h => hcd (inj _ _ (e3.trans (h.trans e4.symm))))
      hxor
  refine ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, ?_⟩
  intro S hS
  rw [hs] at hS
  simp only [mem_insert, mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · rw [e1]; exact c1
  · rw [e2]; exact c2
  · rw [e3]; exact c3
  · rw [e4]; exact c4

end R3
