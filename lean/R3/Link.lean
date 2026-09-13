import R3.Basic
/-!
# The link of a mass-4 vertex  (Lemma 2(a), first half, of R3_equals_10.md)

At a vertex `v` of mass 4 the support consists of exactly four sets `a, b, c, d`, each with
coefficient ±1, each of size ≤ 3 and containing `v`.  The *link sets* `T = S ^^^ 2^v`
(i.e. `S ∖ {v}`) are four distinct subsets of `[n] ∖ {v}` of size ≤ 2 whose xor
(symmetric difference) is `0`, and the four coefficients have product `+1`.
-/
namespace R3
open Finset

lemma card_eq_four {s : Finset ℕ} (h : s.card = 4) :
    ∃ a b c d, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ s = {a, b, c, d} := by
  obtain ⟨a, t, hat, rfl, ht⟩ := card_eq_succ.mp h
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := card_eq_three.mp ht
  refine ⟨a, b, c, d, ?_, ?_, ?_, hbc, hbd, hcd, rfl⟩
  · rintro rfl; exact hat (by simp)
  · rintro rfl; exact hat (by simp)
  · rintro rfl; exact hat (by simp)

/-- removing the bit `v` (present in `S`) lowers the cardinality by one -/
lemma card_xor_two_pow {n S v : ℕ} (hv : v < n) (hS : S.testBit v = true) :
    card n (S ^^^ 2 ^ v) + 1 = card n S := by
  unfold card
  have key : (range n).filter (fun i => S.testBit i) =
      insert v ((range n).filter (fun i => (S ^^^ 2 ^ v).testBit i)) := by
    ext i
    simp only [mem_insert, mem_filter, mem_range]
    constructor
    · rintro ⟨hi, hb⟩
      by_cases hiv : i = v
      · left; exact hiv
      · right; exact ⟨hi, by rw [testBit_xor_two_pow_of_ne hiv]; exact hb⟩
    · rintro (rfl | ⟨hi, hb⟩)
      · exact ⟨hv, hS⟩
      · by_cases hiv : i = v
        · subst hiv; exact ⟨hi, hS⟩
        · exact ⟨hi, by rwa [testBit_xor_two_pow_of_ne hiv] at hb⟩
  rw [key, card_insert_of_notMem]
  simp [mem_filter, Nat.testBit_xor, Nat.testBit_two_pow_self, hS]

/-- a set in the support has size ≤ 3 -/
lemma card_le_three_of_mem_supp {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v S : ℕ}
    (hS : S ∈ supp n N v) : card n S ≤ 3 := by
  obtain ⟨hlt, -, hN⟩ := mem_supp.mp hS
  by_contra h
  push_neg at h
  exact hN (hsol.1 S hlt h)

/-- the link set `S ∖ {v}` of a support set has size ≤ 2 -/
lemma card_link_le_two {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n) {S : ℕ}
    (hS : S ∈ supp n N v) : card n (S ^^^ 2 ^ v) ≤ 2 := by
  have h3 := card_le_three_of_mem_supp hsol hS
  have h := card_xor_two_pow hv (mem_supp.mp hS).2.1
  omega

/-- the link set does not contain `v` -/
lemma link_testBit_self (S v : ℕ) (hS : S.testBit v = true) :
    (S ^^^ 2 ^ v).testBit v = false := by
  rw [Nat.testBit_xor, hS, Nat.testBit_two_pow_self]; rfl

/-- Lemma 2(a), first half: the link of a mass-4 vertex consists of four distinct sets
`a,b,c,d` (each containing `v`, coefficient ±1, size ≤ 3), whose link sets `S ^^^ 2^v`
have size ≤ 2, avoid `v`, and xor to `0`; the four coefficients multiply to `1`. -/
theorem mass_four_link {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n)
    (h4 : mass n N v = 4) :
    ∃ a b c d : ℕ, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      supp n N v = {a, b, c, d} ∧
      (∀ S ∈ ({a, b, c, d} : Finset ℕ), S < 2 ^ n ∧ S.testBit v = true ∧
          (N S = 1 ∨ N S = -1) ∧ card n S ≤ 3 ∧
          card n (S ^^^ 2 ^ v) ≤ 2 ∧ (S ^^^ 2 ^ v).testBit v = false) ∧
      (a ^^^ 2 ^ v) ^^^ (b ^^^ 2 ^ v) ^^^ (c ^^^ 2 ^ v) ^^^ (d ^^^ 2 ^ v) = 0 ∧
      N a * N b * N c * N d = 1 := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs⟩ :=
    card_eq_four (mass_four_card hsol hv h4)
  obtain ⟨hxor, hprod⟩ := mass_four hsol hv h4 hab hac had hbc hbd hcd hs
  refine ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs, ?_, ?_, hprod⟩
  · intro S hS
    rw [← hs] at hS
    obtain ⟨hlt, hb, -⟩ := mem_supp.mp hS
    exact ⟨hlt, hb, mass_four_pm hsol hv h4 S hS, card_le_three_of_mem_supp hsol hS,
      card_link_le_two hsol hv hS, link_testBit_self S v hb⟩
  · rw [xor_two_pow_cancel, Nat.xor_assoc, xor_two_pow_cancel, ← Nat.xor_assoc, hxor]


/-! ## Even degrees: every element lies in an even number of the four sets -/

lemma testBit_xor_four {a b c d j : ℕ} (h : a ^^^ b ^^^ c ^^^ d = 0) :
    ((a.testBit j ^^ b.testBit j) ^^ c.testBit j) ^^ d.testBit j = false := by
  have := congrArg (fun x => x.testBit j) h
  simpa [Nat.testBit_xor, Nat.zero_testBit] using this

lemma four_bool_even {p q r s : Bool} (h : ((p ^^ q) ^^ r) ^^ s = false) :
    (if p then 1 else 0) + (if q then 1 else 0) + (if r then 1 else 0) + (if s then 1 else 0) = 0 ∨
    (if p then 1 else 0) + (if q then 1 else 0) + (if r then 1 else 0) + (if s then 1 else 0) = 2 ∨
    (if p then 1 else 0) + (if q then 1 else 0) + (if r then 1 else 0) + (if s then 1 else 0) = 4 := by
  cases p <;> cases q <;> cases r <;> cases s <;> revert h <;> decide

/-- Lemma 2(a), even-degree form: every bit `j` is set in 0, 2 or 4 of the four support
sets of a mass-4 vertex (for `j = v` it is 4; for `j ≠ v` this is the degree of `j` in
the link) -/
theorem mass_four_even_degree {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n)
    (h4 : mass n N v = 4) {a b c d : ℕ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hs : supp n N v = {a, b, c, d}) (j : ℕ) :
    let deg := (if a.testBit j then 1 else 0) + (if b.testBit j then 1 else 0) +
      (if c.testBit j then 1 else 0) + (if d.testBit j then 1 else 0)
    deg = 0 ∨ deg = 2 ∨ deg = 4 := by
  intro deg
  have hxor := (mass_four hsol hv h4 hab hac had hbc hbd hcd hs).1
  exact four_bool_even (testBit_xor_four (j := j) hxor)

end R3
