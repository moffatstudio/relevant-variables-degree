import R3.Octahedron
/-!
# Step 4 of R3_upper_bound.md: F(12)

`no_crossing_split` is the general form of the argument, stated for any `n`: if the vertex set
splits into `A` and its complement with no support set crossing, and there is a support set on
each side, the solution cannot exist.  It is the Lean form of the hand proof's "f is a sum of
two non-constant functions on disjoint variable sets", and it is reused throughout F(11).

For F(12): `octahedron_closure` splits the 12 vertices into a 6-set `A` and its complement so
that no support triple crosses.  Pick a support triple `S0` inside `A` and one, `T0`, outside.
Their union `U = S0 ||| T0` is also their symmetric difference, and it is attained by
*exactly* the two ordered pairs `(S0,T0)` and `(T0,S0)`: any other pair would have to put a
support triple on both sides of `A`.  CondII at `U` therefore reads `2 n_{S0} n_{T0} = 0`,
contradicting `n_{S0}, n_{T0} ≠ 0`.  Hence `F 12`, i.e. `R_3 ≤ 11`.
-/
namespace R3
open Finset

lemma xor_cancel_left {a x y : ℕ} (h : a ^^^ x = a ^^^ y) : x = y := by
  have h2 := congrArg (fun z => a ^^^ z) h
  simpa [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] using h2

/-- **The disjoint-sum contradiction, for any `n`.**  If the support of a solution never
crosses between `A` and its complement, and there is a nonzero coefficient on each side, the
solution does not exist: `CondII` at the union of the two sets has exactly two terms.
This is the Lean form of "a sum of two non-constant functions on disjoint variable sets is
never Boolean" (R3_upper_bound.md Step 4), and it is reused for every such step of F(11). -/
theorem no_crossing_split {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {A : Finset ℕ}
    {S0 T0 i w : ℕ}
    (hS0lt : S0 < 2 ^ n) (hS0N : N S0 ≠ 0) (hS0bit : S0.testBit i = true)
    (hS0A : ∀ j, S0.testBit j = true → j ∈ A)
    (hT0lt : T0 < 2 ^ n) (hT0N : N T0 ≠ 0) (hT0bit : T0.testBit w = true)
    (hT0A : ∀ j, T0.testBit j = true → j ∉ A)
    (hcross : ∀ S, S < 2 ^ n → N S ≠ 0 →
      (∀ j, S.testBit j = true → j ∈ A) ∨ (∀ j, S.testBit j = true → j ∉ A)) :
    False := by
  have h0A : i ∈ A := hS0A i hS0bit
  have hwA : w ∉ A := hT0A w hT0bit
  -- the union U of the two sets is their symmetric difference
  have hUbit : ∀ j, (S0 ||| T0).testBit j = (S0.testBit j || T0.testBit j) :=
    fun j => Nat.testBit_or _ _ _
  have hxor : S0 ^^^ T0 = S0 ||| T0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_xor, hUbit]
    by_cases h1 : S0.testBit j = true
    · by_cases h2 : T0.testBit j = true
      · exact absurd (hS0A j h1) (hT0A j h2)
      · have h2' : T0.testBit j = false := by simpa using h2
        rw [h1, h2']; rfl
    · have h1' : S0.testBit j = false := by simpa using h1
      rw [h1']
      cases T0.testBit j <;> rfl
  -- only the two ordered pairs (S0,T0), (T0,S0) have symmetric difference U
  have huniq : ∀ S T, S < 2 ^ n → T < 2 ^ n → S ^^^ T = S0 ||| T0 → N S ≠ 0 → N T ≠ 0 →
      (S = S0 ∧ T = T0) ∨ (S = T0 ∧ T = S0) := by
    intro S T hSlt hTlt hST hSN hTN
    have hbit : ∀ j, ((S.testBit j).xor (T.testBit j)) = (S0.testBit j || T0.testBit j) := by
      intro j; rw [← Nat.testBit_xor, hST, hUbit]
    rcases hcross S hSlt hSN with hSin | hSout <;> rcases hcross T hTlt hTN with hTin | hTout
    · -- both inside A: the bit w of U is not attained
      exfalso
      have hSw : S.testBit w = false := by
        by_contra hcon; exact hwA (hSin w (by simpa using hcon))
      have hTw : T.testBit w = false := by
        by_contra hcon; exact hwA (hTin w (by simpa using hcon))
      have hb := hbit w
      rw [hSw, hTw, hT0bit] at hb
      simp at hb
    · -- S inside, T outside
      left
      constructor
      · apply Nat.eq_of_testBit_eq
        intro j
        by_cases hjA : j ∈ A
        · have hTj : T.testBit j = false := by
            by_contra hcon; exact hTout j (by simpa using hcon) hjA
          have hT0j : T0.testBit j = false := by
            by_contra hcon; exact hT0A j (by simpa using hcon) hjA
          have hb := hbit j
          rw [hTj, hT0j] at hb
          simpa using hb
        · have hSj : S.testBit j = false := by
            by_contra hcon; exact hjA (hSin j (by simpa using hcon))
          have hS0j : S0.testBit j = false := by
            by_contra hcon; exact hjA (hS0A j (by simpa using hcon))
          rw [hSj, hS0j]
      · apply Nat.eq_of_testBit_eq
        intro j
        by_cases hjA : j ∈ A
        · have hTj : T.testBit j = false := by
            by_contra hcon; exact hTout j (by simpa using hcon) hjA
          have hT0j : T0.testBit j = false := by
            by_contra hcon; exact hT0A j (by simpa using hcon) hjA
          rw [hTj, hT0j]
        · have hSj : S.testBit j = false := by
            by_contra hcon; exact hjA (hSin j (by simpa using hcon))
          have hS0j : S0.testBit j = false := by
            by_contra hcon; exact hjA (hS0A j (by simpa using hcon))
          have hb := hbit j
          rw [hSj, hS0j] at hb
          simpa using hb
    · -- S outside, T inside
      right
      constructor
      · apply Nat.eq_of_testBit_eq
        intro j
        by_cases hjA : j ∈ A
        · have hSj : S.testBit j = false := by
            by_contra hcon; exact hSout j (by simpa using hcon) hjA
          have hT0j : T0.testBit j = false := by
            by_contra hcon; exact hT0A j (by simpa using hcon) hjA
          rw [hSj, hT0j]
        · have hTj : T.testBit j = false := by
            by_contra hcon; exact hjA (hTin j (by simpa using hcon))
          have hS0j : S0.testBit j = false := by
            by_contra hcon; exact hjA (hS0A j (by simpa using hcon))
          have hb := hbit j
          rw [hTj, hS0j] at hb
          simpa using hb
      · apply Nat.eq_of_testBit_eq
        intro j
        by_cases hjA : j ∈ A
        · have hSj : S.testBit j = false := by
            by_contra hcon; exact hSout j (by simpa using hcon) hjA
          have hT0j : T0.testBit j = false := by
            by_contra hcon; exact hT0A j (by simpa using hcon) hjA
          have hb := hbit j
          rw [hSj, hT0j] at hb
          simpa using hb
        · have hTj : T.testBit j = false := by
            by_contra hcon; exact hjA (hTin j (by simpa using hcon))
          have hS0j : S0.testBit j = false := by
            by_contra hcon; exact hjA (hS0A j (by simpa using hcon))
          rw [hTj, hS0j]
    · -- both outside A: the bit 0 of U is not attained
      exfalso
      have hS0' : S.testBit i = false := by
        by_contra hcon; exact hSout i (by simpa using hcon) h0A
      have hT0' : T.testBit i = false := by
        by_contra hcon; exact hTout i (by simpa using hcon) h0A
      have hb := hbit i
      rw [hS0', hT0', hS0bit] at hb
      simp at hb
  -- CondII at U has exactly the two terms
  have hS0T0 : S0 ≠ T0 := by
    intro h
    rw [h] at hS0bit
    exact hT0A i hS0bit h0A
  have hUlt : S0 ||| T0 < 2 ^ n := Nat.or_lt_two_pow hS0lt hT0lt
  have hUpos : 0 < S0 ||| T0 := by
    rcases Nat.eq_zero_or_pos (S0 ||| T0) with h | h
    · exfalso
      have hb := hUbit i
      rw [h, hS0bit] at hb
      simp at hb
    · exact h
  have hII := hsol.2.2.1 (S0 ||| T0) hUpos hUlt
  have hmemS0 : S0 ∈ range (2 ^ n) := mem_range.mpr hS0lt
  have hmemT0 : T0 ∈ range (2 ^ n) := mem_range.mpr hT0lt
  have hpairsub : ({S0, T0} : Finset ℕ) ⊆ range (2 ^ n) := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx'
    · exact hmemS0
    · rw [mem_singleton] at hx'; subst hx'; exact hmemT0
  have hzero : ∀ S ∈ range (2 ^ n), S ∉ ({S0, T0} : Finset ℕ) →
      (∑ T ∈ range (2 ^ n), if S ^^^ T = S0 ||| T0 then N S * N T else 0) = 0 := by
    intro S hS hSni
    refine Finset.sum_eq_zero fun T hT => ?_
    split_ifs with hc
    · by_cases hNS : N S = 0
      · rw [hNS, zero_mul]
      by_cases hNT : N T = 0
      · rw [hNT, mul_zero]
      exfalso
      rcases huniq S T (mem_range.mp hS) (mem_range.mp hT) hc hNS hNT with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hSni (by simp)
      · exact hSni (by simp)
    · rfl
  have keyS0 : ∀ T ∈ range (2 ^ n), T ≠ T0 →
      (if S0 ^^^ T = S0 ||| T0 then N S0 * N T else 0) = 0 := by
    intro T _ hTne
    exact if_neg fun hc => hTne (xor_cancel_left (hc.trans hxor.symm))
  have hxor' : T0 ^^^ S0 = S0 ||| T0 := by rw [Nat.xor_comm]; exact hxor
  have keyT0 : ∀ T ∈ range (2 ^ n), T ≠ S0 →
      (if T0 ^^^ T = S0 ||| T0 then N T0 * N T else 0) = 0 := by
    intro T _ hTne
    exact if_neg fun hc => hTne (xor_cancel_left (hc.trans hxor'.symm))
  rw [← Finset.sum_subset hpairsub hzero, Finset.sum_pair hS0T0,
    Finset.sum_eq_single_of_mem T0 hmemT0 keyS0, Finset.sum_eq_single_of_mem S0 hmemS0 keyT0,
    if_pos hxor, if_pos hxor', mul_comm (N T0) (N S0)] at hII
  have hx : N S0 * N T0 = 0 := by linarith
  rcases mul_eq_zero.mp hx with h | h
  · exact hS0N h
  · exact hT0N h

/-- **F(12): no Boolean function of degree 3 has 12 relevant variables.**  Equivalently
`R_3 ≤ 11`. -/
theorem F_twelve : F 12 := by
  rintro ⟨N, hsol⟩
  have h0 : (0 : ℕ) < 12 := by norm_num
  obtain ⟨A, hcard, hAsub, h0A, hcross⟩ := octahedron_closure hsol h0
  -- a support triple inside A, through the vertex 0
  obtain ⟨S0, hS0lt, hS0bit, hS0N⟩ := hsol.2.2.2 0 h0
  have hS0A : ∀ j, S0.testBit j = true → j ∈ A := by
    rcases hcross S0 hS0lt hS0N with h | h
    · exact h
    · exact absurd h0A (h 0 hS0bit)
  -- A has six of the twelve vertices, so some vertex w lies outside it
  have hss : A ⊂ range 12 := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hAsub, ?_⟩
    intro h
    rw [h, card_range] at hcard
    omega
  obtain ⟨w, hwr, hwA⟩ := Finset.exists_of_ssubset hss
  obtain ⟨T0, hT0lt, hT0bit, hT0N⟩ := hsol.2.2.2 w (mem_range.mp hwr)
  have hT0A : ∀ j, T0.testBit j = true → j ∉ A := by
    rcases hcross T0 hT0lt hT0N with h | h
    · exact absurd (h w hT0bit) hwA
    · exact h
  exact no_crossing_split hsol hS0lt hS0N hS0bit hS0A hT0lt hT0N hT0bit hT0A hcross

end R3
