import R3.LinkSix
import R3.Final
import R3.DeltaFour
/-!
# The case `delta = 2` of F(11)  (R3_equals_10.md, "Case delta = 2")

`delta = 2` is the case where exactly one vertex has mass 6 and the other ten have mass 4.
The bookkeeping identity `e + delta = 48 - 4n` then forces the lower-order weight to be `2`,
i.e. either one linear `±1` term or two unit quadratics.

This file currently certifies:
* `delta_two_weight` — the lower-order weight is exactly `2`;
* `three_quadratics_absurd` — three distinct quadratic terms are impossible;
* `two_quadratics_at` — with no linear/constant term, a mass-4 endpoint of a quadratic
  carries exactly two quadratics (the `L3` step of the hand proof);
* `eleven_delta_two_quad` — the "two quadratics" branch of the case is impossible.
-/
namespace R3
open Finset

/-! ## Finset helpers -/

lemma card_quad_eq_dtwo {T1 T2 T3 T4 : ℕ} (d12 : T1 ≠ T2) (d13 : T1 ≠ T3) (d14 : T1 ≠ T4)
    (d23 : T2 ≠ T3) (d24 : T2 ≠ T4) (d34 : T3 ≠ T4) :
    ({T1, T2, T3, T4} : Finset ℕ).card = 4 := by
  rw [card_insert_of_notMem (by simp [d12, d13, d14]),
    card_insert_of_notMem (by simp [d23, d24]), card_pair d34]

/-- four distinct values drawn from a four-element list exhaust it -/
lemma four_distinct_exhaust {A B C D T1 T2 T3 T4 : ℕ}
    (d12 : T1 ≠ T2) (d13 : T1 ≠ T3) (d14 : T1 ≠ T4)
    (d23 : T2 ≠ T3) (d24 : T2 ≠ T4) (d34 : T3 ≠ T4)
    (h1 : T1 = A ∨ T1 = B ∨ T1 = C ∨ T1 = D)
    (h2 : T2 = A ∨ T2 = B ∨ T2 = C ∨ T2 = D)
    (h3 : T3 = A ∨ T3 = B ∨ T3 = C ∨ T3 = D)
    (h4 : T4 = A ∨ T4 = B ∨ T4 = C ∨ T4 = D) :
    ∀ X ∈ ({A, B, C, D} : Finset ℕ), X = T1 ∨ X = T2 ∨ X = T3 ∨ X = T4 := by
  have hsub : ({T1, T2, T3, T4} : Finset ℕ) ⊆ ({A, B, C, D} : Finset ℕ) := by
    intro X hX
    simp only [mem_insert, mem_singleton] at hX ⊢
    rcases hX with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hc : ({A, B, C, D} : Finset ℕ).card ≤ ({T1, T2, T3, T4} : Finset ℕ).card := by
    rw [card_quad_eq_dtwo d12 d13 d14 d23 d24 d34]
    exact card_quad_le A B C D
  have heq := eq_of_subset_of_card_le hsub hc
  intro X hX
  rw [← heq] at hX
  simpa only [mem_insert, mem_singleton] using hX

/-! ## The lower-order weight is 2 -/

/-- In the `delta = 2` case (one vertex of mass 6, the rest of mass 4) the lower-order
weight `∑_S (3 - |S|) n_S²` equals `2`. -/
theorem delta_two_weight {N : ℕ → ℤ} (hsol : IsSol 11 N) {v : ℕ} (hv : v < 11)
    (h6 : mass 11 N v = 6) (hrest : ∀ w, w < 11 → w ≠ v → mass 11 N w = 4) :
    ∑ S ∈ range (2 ^ 11), ((3 : ℤ) - card 11 S) * (N S) ^ 2 = 2 := by
  have hb := bookkeeping hsol
  have hv' : v ∈ range 11 := mem_range.mpr hv
  rw [← add_sum_erase (range 11) _ hv'] at hb
  have hz : ∑ w ∈ (range 11).erase v, (mass 11 N w - 4) = 0 := by
    apply sum_eq_zero
    intro w hw
    rw [hrest w (mem_range.mp (mem_of_mem_erase hw)) (ne_of_mem_erase hw)]
    ring
  rw [hz, h6] at hb
  push_cast at hb
  have h2048 : (2 : ℕ) ^ 11 = 2048 := by norm_num
  rw [h2048]
  linarith

/-! ## Three quadratics are too heavy -/

lemma quad_term_eq {n S : ℕ} {N : ℕ → ℤ} (hc : card n S = 2) :
    ((3 : ℤ) - card n S) * (N S) ^ 2 = (N S) ^ 2 := by rw [hc]; push_cast; ring

/-- three distinct sets of size 2 with nonzero coefficients carry lower-order weight ≥ 3 -/
theorem three_quadratics_absurd {N : ℕ → ℤ} (hsol : IsSol 11 N)
    (hD : ∑ S ∈ range (2 ^ 11), ((3 : ℤ) - card 11 S) * (N S) ^ 2 = 2)
    {S1 S2 S3 : ℕ} (h1 : S1 < 2 ^ 11) (h2 : S2 < 2 ^ 11) (h3 : S3 < 2 ^ 11)
    (c1 : card 11 S1 = 2) (c2 : card 11 S2 = 2) (c3 : card 11 S3 = 2)
    (n1 : N S1 ≠ 0) (n2 : N S2 ≠ 0) (n3 : N S3 ≠ 0)
    (d12 : S1 ≠ S2) (d13 : S1 ≠ S3) (d23 : S2 ≠ S3) : False := by
  have hsub : ({S1, S2, S3} : Finset ℕ) ⊆ range (2 ^ 11) := by
    intro X hX
    simp only [mem_insert, mem_singleton] at hX
    rcases hX with rfl | rfl | rfl <;> exact mem_range.mpr (by assumption)
  have hnn : ∀ S ∈ range (2 ^ 11), S ∉ ({S1, S2, S3} : Finset ℕ) →
      0 ≤ ((3 : ℤ) - card 11 S) * (N S) ^ 2 :=
    fun S hS _ => delta_term_nonneg hsol (mem_range.mp hS)
  have hle := sum_le_sum_of_subset_of_nonneg hsub hnn
  rw [hD] at hle
  rw [sum_insert (by simp [d12, d13]), sum_pair d23, quad_term_eq c1, quad_term_eq c2,
    quad_term_eq c3] at hle
  have a1 := one_le_sq_of_ne_zero n1
  have a2 := one_le_sq_of_ne_zero n2
  have a3 := one_le_sq_of_ne_zero n3
  omega

/-! ## Two quadratics at every mass-4 endpoint (the `L3` step) -/

lemma pair_lt_dtwo {n p q : ℕ} (hp : p < n) (hq : q < n) (hpq : p ≠ q) : pair p q < 2 ^ n := by
  rw [← two_pow_xor_two_pow hpq]
  exact Nat.xor_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) hp)
    (Nat.pow_lt_pow_right (by norm_num) hq)

lemma two_pow_lt_iff {n a : ℕ} (h : (2 : ℕ) ^ a < 2 ^ n) : a < n :=
  (Nat.pow_lt_pow_iff_right (by norm_num)).mp h

/-- **The `L3` step of the `delta = 2` two-quadratics branch.**  If there is no linear or
constant term, a mass-4 vertex `u` lying on a quadratic lies on *two* distinct quadratics. -/
theorem two_quadratics_at {N : ℕ → ℤ} (hsol : IsSol 11 N)
    (hnolin : ∀ S, S < 2 ^ 11 → N S ≠ 0 → 2 ≤ card 11 S)
    {u w : ℕ} (hu : u < 11) (hw : w < 11) (huw : u ≠ w)
    (h4 : mass 11 N u = 4) (hQ : N (pair u w) ≠ 0) :
    ∃ a b, a < 11 ∧ b < 11 ∧ a ≠ b ∧ a ≠ u ∧ b ≠ u ∧
      N (pair u a) ≠ 0 ∧ N (pair u b) ≠ 0 := by
  obtain ⟨S1, S2, S3, S4, e12, e13, e14, e23, e24, e34, hs, hall, hxor, -⟩ :=
    mass_four_link hsol hu h4
  set T1 := S1 ^^^ 2 ^ u with hT1
  set T2 := S2 ^^^ 2 ^ u with hT2
  set T3 := S3 ^^^ 2 ^ u with hT3
  set T4 := S4 ^^^ 2 ^ u with hT4
  have inj : ∀ x y : ℕ, x ^^^ 2 ^ u = y ^^^ 2 ^ u → x = y := by
    intro x y h
    have := congrArg (fun z => z ^^^ 2 ^ u) h
    simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this
  have d12 : T1 ≠ T2 := fun h => e12 (inj _ _ h)
  have d13 : T1 ≠ T3 := fun h => e13 (inj _ _ h)
  have d14 : T1 ≠ T4 := fun h => e14 (inj _ _ h)
  have d23 : T2 ≠ T3 := fun h => e23 (inj _ _ h)
  have d24 : T2 ≠ T4 := fun h => e24 (inj _ _ h)
  have d34 : T3 ≠ T4 := fun h => e34 (inj _ _ h)
  have h2u : (2 : ℕ) ^ u < 2 ^ 11 := Nat.pow_lt_pow_right (by norm_num) hu
  have hlt : ∀ S ∈ ({S1, S2, S3, S4} : Finset ℕ), S ^^^ 2 ^ u < 2 ^ 11 :=
    fun S hS => Nat.xor_lt_two_pow (hall S hS).1 h2u
  have hcard : ∀ S ∈ ({S1, S2, S3, S4} : Finset ℕ), card 11 (S ^^^ 2 ^ u) ≤ 2 :=
    fun S hS => (hall S hS).2.2.2.2.1
  have hty := link_types (hlt S1 (by simp)) (hlt S2 (by simp)) (hlt S3 (by simp))
    (hlt S4 (by simp)) (hcard S1 (by simp)) (hcard S2 (by simp)) (hcard S3 (by simp))
    (hcard S4 (by simp)) d12 d13 d14 d23 d24 d34 hxor
  -- the given quadratic is one of the four support sets and its link set is a singleton
  have hQlt : pair u w < 2 ^ 11 := pair_lt_dtwo hu hw huw
  have hQmem : pair u w ∈ supp 11 N u :=
    mem_supp.mpr ⟨hQlt, mem_pair_iff.mpr (Or.inl rfl), hQ⟩
  have hQlink : pair u w ^^^ 2 ^ u = 2 ^ w := pair_xor_two_pow_left huw
  have hQin : pair u w = S1 ∨ pair u w = S2 ∨ pair u w = S3 ∨ pair u w = S4 := by
    rw [hs] at hQmem
    simpa only [mem_insert, mem_singleton] using hQmem
  have hsing : T1 = 2 ^ w ∨ T2 = 2 ^ w ∨ T3 = 2 ^ w ∨ T4 = 2 ^ w := by
    rcases hQin with h | h | h | h
    · left; rw [hT1, ← h, hQlink]
    · right; left; rw [hT2, ← h, hQlink]
    · right; right; left; rw [hT3, ← h, hQlink]
    · right; right; right; rw [hT4, ← h, hQlink]
  -- no support set is a singleton, so `L2` is impossible
  have hno0 : ∀ i, i ∈ ({T1, T2, T3, T4} : Finset ℕ) → i ≠ 0 := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    have key : ∀ S ∈ ({S1, S2, S3, S4} : Finset ℕ), S ^^^ 2 ^ u ≠ 0 := by
      intro S hS hz
      have hSu : S = 2 ^ u := by
        have := congrArg (fun z => z ^^^ 2 ^ u) hz
        simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this
      have hSmem : S ∈ supp 11 N u := by rw [hs]; exact hS
      have := hnolin S (hall S hS).1 (mem_supp.mp hSmem).2.2
      rw [hSu, card_two_pow hu] at this
      omega
    rcases hi with rfl | rfl | rfl | rfl
    · exact key S1 (by simp)
    · exact key S2 (by simp)
    · exact key S3 (by simp)
    · exact key S4 (by simp)
  -- extract the two singletons from the L3 shape
  have hL3 : ∃ a b, a ≠ b ∧ (2 : ℕ) ^ a ∈ ({T1, T2, T3, T4} : Finset ℕ) ∧
      (2 : ℕ) ^ b ∈ ({T1, T2, T3, T4} : Finset ℕ) := by
    rcases hty with ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, o1, o2, o3, o4⟩ |
      ⟨a, b, hab, m1, m2, m3, m4⟩ | ⟨a, b, c, hab, hac, hbc, m1, m2, m3, m4⟩ |
      ⟨a, b, c, hab, hac, hbc, m1, m2, m3, m4⟩
    · -- L1: every link set is a pair, but one of them is the singleton 2^w
      exfalso
      have kill : ∀ T, OnCycle p q r s T → T ≠ 2 ^ w := by
        intro T hT
        rcases hT with rfl | rfl | rfl | rfl
        · exact pair_ne_two_pow hpq
        · exact pair_ne_two_pow hqr
        · exact pair_ne_two_pow hrs
        · exact pair_ne_two_pow (Ne.symm hps)
      rcases hsing with h | h | h | h
      · exact kill T1 o1 h
      · exact kill T2 o2 h
      · exact kill T3 o3 h
      · exact kill T4 o4 h
    · -- L2: the value 0 occurs among the four link sets
      exfalso
      have hex := four_distinct_exhaust d12 d13 d14 d23 d24 d34 m1 m2 m3 m4 0 (by simp)
      rcases hex with h | h | h | h
      · exact hno0 T1 (by simp) h.symm
      · exact hno0 T2 (by simp) h.symm
      · exact hno0 T3 (by simp) h.symm
      · exact hno0 T4 (by simp) h.symm
    · -- L3: the two singletons 2^a, 2^b both occur
      refine ⟨a, b, ?_, ?_, ?_⟩
      · intro hh; exact hab hh
      · have hex := four_distinct_exhaust d12 d13 d14 d23 d24 d34 m1 m2 m3 m4 (2 ^ a)
          (by simp)
        rcases hex with h | h | h | h <;> rw [h] <;> simp
      · have hex := four_distinct_exhaust d12 d13 d14 d23 d24 d34 m1 m2 m3 m4 (2 ^ b)
          (by simp)
        rcases hex with h | h | h | h <;> rw [h] <;> simp
    · -- L4: every link set is 0 or a pair, but one of them is the singleton 2^w
      exfalso
      have kill : ∀ T, IsL4 a b c T → T ≠ 2 ^ w := by
        intro T hT
        rcases hT with rfl | rfl | rfl | rfl
        · intro hh; exact (Nat.two_pow_pos w).ne' hh.symm
        · exact pair_ne_two_pow hab
        · exact pair_ne_two_pow hbc
        · exact pair_ne_two_pow hac
      rcases hsing with h | h | h | h
      · exact kill T1 m1 h
      · exact kill T2 m2 h
      · exact kill T3 m3 h
      · exact kill T4 m4 h
  obtain ⟨a, b, hab, hma, hmb⟩ := hL3
  -- turn a link singleton back into a quadratic at u
  have back : ∀ x, (2 : ℕ) ^ x ∈ ({T1, T2, T3, T4} : Finset ℕ) →
      x < 11 ∧ x ≠ u ∧ N (pair u x) ≠ 0 := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    have key : ∀ S ∈ ({S1, S2, S3, S4} : Finset ℕ), S ^^^ 2 ^ u = 2 ^ x →
        x < 11 ∧ x ≠ u ∧ N (pair u x) ≠ 0 := by
      intro S hS hSx
      have hSmem : S ∈ supp 11 N u := by rw [hs]; exact hS
      have hbit := (hall S hS).2.2.2.2.2
      rw [hSx] at hbit
      have hxu : x ≠ u := by
        intro hh; rw [hh, Nat.testBit_two_pow_self] at hbit; exact Bool.noConfusion hbit
      have hxlt : x < 11 := two_pow_lt_iff (hSx ▸ hlt S hS)
      have hSeq : S = pair u x := by
        have := congrArg (fun z => z ^^^ 2 ^ u) hSx
        simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
        rw [this, two_pow_xor_two_pow hxu, pair_comm]
      refine ⟨hxlt, hxu, ?_⟩
      rw [← hSeq]
      exact (mem_supp.mp hSmem).2.2
    rcases hx with h | h | h | h
    · exact key S1 (by simp) h.symm
    · exact key S2 (by simp) h.symm
    · exact key S3 (by simp) h.symm
    · exact key S4 (by simp) h.symm
  obtain ⟨ha1, ha2, ha3⟩ := back a hma
  obtain ⟨hb1, hb2, hb3⟩ := back b hmb
  exact ⟨a, b, ha1, hb1, hab, ha2, hb2, ha3, hb3⟩

/-! ## The "two quadratics" branch of `delta = 2` -/

/-- with no linear or constant term, some quadratic term exists (the weight `2` has to
live somewhere) -/
lemma exists_quadratic {N : ℕ → ℤ} (hsol : IsSol 11 N)
    (hnolin : ∀ S, S < 2 ^ 11 → N S ≠ 0 → 2 ≤ card 11 S)
    (hD : ∑ S ∈ range (2 ^ 11), ((3 : ℤ) - card 11 S) * (N S) ^ 2 = 2) :
    ∃ S, S < 2 ^ 11 ∧ N S ≠ 0 ∧ card 11 S = 2 := by
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ S ∈ range (2 ^ 11), ((3 : ℤ) - card 11 S) * (N S) ^ 2 = 0 := by
    intro S hS
    have hSlt := mem_range.mp hS
    by_cases hN : N S = 0
    · rw [hN]; ring
    · have h2 := hnolin S hSlt hN
      have h3 : card 11 S ≤ 3 := by
        by_contra hc
        push_neg at hc
        exact hN (hsol.1 S hSlt hc)
      have hne2 : card 11 S ≠ 2 := hcon S hSlt hN
      have : card 11 S = 3 := by omega
      rw [this]; push_cast; ring
  rw [sum_congr rfl hzero, sum_const_zero] at hD
  exact absurd hD (by norm_num)

/-- three distinct quadratics, assembled from two at `u` and two at `a` -/
lemma quad_three_of {N : ℕ → ℤ} (hsol : IsSol 11 N)
    (hD : ∑ S ∈ range (2 ^ 11), ((3 : ℤ) - card 11 S) * (N S) ^ 2 = 2)
    {u a b e f : ℕ} (hu : u < 11) (ha : a < 11) (hb : b < 11) (he : e < 11) (hf : f < 11)
    (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u)
    (hef : e ≠ f) (hea : e ≠ a) (hfa : f ≠ a)
    (Na : N (pair u a) ≠ 0) (Nb : N (pair u b) ≠ 0)
    (Nae : N (pair a e) ≠ 0) (Naf : N (pair a f) ≠ 0) : False := by
  have cua : card 11 (pair u a) = 2 := card_pair_eq hu ha (Ne.symm hau)
  have cub : card 11 (pair u b) = 2 := card_pair_eq hu hb (Ne.symm hbu)
  have cae : card 11 (pair a e) = 2 := card_pair_eq ha he (Ne.symm hea)
  have caf : card 11 (pair a f) = 2 := card_pair_eq ha hf (Ne.symm hfa)
  have lua : pair u a < 2 ^ 11 := pair_lt_dtwo hu ha (Ne.symm hau)
  have lub : pair u b < 2 ^ 11 := pair_lt_dtwo hu hb (Ne.symm hbu)
  have lae : pair a e < 2 ^ 11 := pair_lt_dtwo ha he (Ne.symm hea)
  have laf : pair a f < 2 ^ 11 := pair_lt_dtwo ha hf (Ne.symm hfa)
  have dab : pair u a ≠ pair u b := by
    rw [ne_eq, pair_eq_iff]; push_neg; constructor <;> intro h <;> omega
  have dbe : pair u b ≠ pair a e := by
    rw [ne_eq, pair_eq_iff]; push_neg; constructor <;> intro h <;> omega
  have dbf : pair u b ≠ pair a f := by
    rw [ne_eq, pair_eq_iff]; push_neg; constructor <;> intro h <;> omega
  by_cases hq : pair a e = pair u a
  · -- then `pair a f` is the third quadratic
    have daf : pair u a ≠ pair a f := by
      rw [pair_eq_iff] at hq
      rw [ne_eq, pair_eq_iff]; push_neg
      constructor <;> intro h <;> omega
    exact three_quadratics_absurd hsol hD lua lub laf cua cub caf Na Nb Naf dab daf dbf
  · have dae : pair u a ≠ pair a e := fun h => hq h.symm
    exact three_quadratics_absurd hsol hD lua lub lae cua cub cae Na Nb Nae dab dae dbe

/-- **The "two quadratics" branch of `delta = 2` is impossible.** -/
theorem eleven_delta_two_quad {N : ℕ → ℤ} (hsol : IsSol 11 N) {v : ℕ} (hv : v < 11)
    (h6 : mass 11 N v = 6) (hrest : ∀ w, w < 11 → w ≠ v → mass 11 N w = 4)
    (hnolin : ∀ S, S < 2 ^ 11 → N S ≠ 0 → 2 ≤ card 11 S) : False := by
  have hD := delta_two_weight hsol hv h6 hrest
  obtain ⟨Q, hQlt, hQN, hQc⟩ := exists_quadratic hsol hnolin hD
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := exists_pair_of_card_two hQlt hQc
  -- the key step, applied at an endpoint different from `v`
  have key : ∀ u w, u < 11 → w < 11 → u ≠ w → u ≠ v → N (pair u w) ≠ 0 → False := by
    intro u w hu hw huw huv hQ
    obtain ⟨a, b, ha, hb, hab, hau, hbu, Na, Nb⟩ :=
      two_quadratics_at hsol hnolin hu hw huw (hrest u hu huv) hQ
    -- at least one of `a`, `b` differs from `v`; work at that vertex
    have step : ∀ x y, x < 11 → y < 11 → x ≠ y → x ≠ u → y ≠ u → x ≠ v →
        N (pair u x) ≠ 0 → N (pair u y) ≠ 0 → False := by
      intro x y hx hy hxy hxu hyu hxv Nx Ny
      have hxQ : N (pair x u) ≠ 0 := by rwa [pair_comm]
      obtain ⟨e, f, he, hf, hef, hex, hfx, Ne', Nf'⟩ :=
        two_quadratics_at hsol hnolin hx hu hxu (hrest x hx hxv) hxQ
      exact quad_three_of hsol hD hu hx hy he hf hxy hxu hyu hef hex hfx Nx Ny Ne' Nf'
    by_cases hav : a = v
    · exact step b a hb ha (Ne.symm hab) hbu hau (by rw [← hav] at huv ⊢; omega) Nb Na
    · exact step a b ha hb hab hau hbu hav Na Nb
  by_cases hpv : p = v
  · exact key q p hq hp (Ne.symm hpq) (by omega) (by rwa [pair_comm])
  · exact key p q hp hq hpq hpv hQN

/-! ## The "one linear term" branch: the structure of the lower-order part -/

/-- If a lower-order term of size ≤ 1 exists in the `delta = 2` case then it is a *linear*
term with coefficient `±1`, and every other support set is a cubic: there are no quadratics
and no second lower-order term. -/
theorem delta_two_linear {N : ℕ → ℤ} (hsol : IsSol 11 N)
    (hD : ∑ S ∈ range (2 ^ 11), ((3 : ℤ) - card 11 S) * (N S) ^ 2 = 2)
    {L : ℕ} (hL : L < 2 ^ 11) (hLN : N L ≠ 0) (hLc : card 11 L ≤ 1) :
    card 11 L = 1 ∧ (N L = 1 ∨ N L = -1) ∧
      ∀ S, S < 2 ^ 11 → N S ≠ 0 → S ≠ L → card 11 S = 3 := by
  have hmem : L ∈ range (2 ^ 11) := mem_range.mpr hL
  have hsplit : ∑ S ∈ (range (2 ^ 11)).erase L, ((3 : ℤ) - card 11 S) * (N S) ^ 2 +
      ((3 : ℤ) - card 11 L) * (N L) ^ 2 = 2 := by
    rw [sum_erase_add _ _ hmem]; exact hD
  have hnn : 0 ≤ ∑ S ∈ (range (2 ^ 11)).erase L, ((3 : ℤ) - card 11 S) * (N S) ^ 2 :=
    sum_nonneg (fun S hS => delta_term_nonneg hsol (mem_range.mp (mem_of_mem_erase hS)))
  set R := ∑ S ∈ (range (2 ^ 11)).erase L, ((3 : ℤ) - card 11 S) * (N S) ^ 2 with hRdef
  have hsq : (1 : ℤ) ≤ (N L) ^ 2 := one_le_sq_of_ne_zero hLN
  have hc1 : card 11 L = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hLc with h0 | h1
    · exfalso
      rw [h0] at hsplit
      push_cast at hsplit
      linarith
    · exact h1
  rw [hc1] at hsplit
  push_cast at hsplit
  have hNL : (N L) ^ 2 = 1 := by linarith
  have hR0 : R = 0 := by linarith
  refine ⟨hc1, pm_one_of_sq_le_three hLN (by omega), ?_⟩
  intro S hSlt hSN hSL
  have hSmem : S ∈ (range (2 ^ 11)).erase L := mem_erase.mpr ⟨hSL, mem_range.mpr hSlt⟩
  have hterm := (sum_eq_zero_iff_of_nonneg
    (fun T hT => delta_term_nonneg hsol (mem_range.mp (mem_of_mem_erase hT)))).mp
    (hRdef ▸ hR0) S hSmem
  have hsq2 : (1 : ℤ) ≤ (N S) ^ 2 := one_le_sq_of_ne_zero hSN
  have hz : ((3 : ℤ) - card 11 S) = 0 := by
    rcases mul_eq_zero.mp hterm with h | h
    · exact h
    · exact absurd h (by linarith)
  have h3 : (card 11 S : ℤ) = 3 := by linarith
  exact_mod_cast h3

/-! ## The "one linear term" branch: shared infrastructure

Throughout this section the hypothesis bundle is: `N` is an 11-variable solution, `l` is a
vertex with `N (2 ^ l) ≠ 0`, and every other support set is a triple (`hall`).  This is
exactly the output of `delta_two_linear`.
-/

/-- with only one linear term below the top level there is no quadratic term -/
lemma one_linear_no_quad {N : ℕ → ℤ} {l : ℕ}
    (hall : ∀ S, S < 2 ^ 11 → N S ≠ 0 → S = 2 ^ l ∨ card 11 S = 3)
    {u w : ℕ} (hu : u < 11) (hw : w < 11) (huw : u ≠ w) : N (pair u w) = 0 := by
  by_contra hne
  rcases hall _ (pair_lt_two_pow hu hw) hne with h | h
  · exact pair_ne_two_pow huw h
  · rw [card_pair_eq hu hw huw] at h; omega

/-- with only one linear term below the top level there is no constant term -/
lemma one_linear_no_const {N : ℕ → ℤ} {l : ℕ}
    (hall : ∀ S, S < 2 ^ 11 → N S ≠ 0 → S = 2 ^ l ∨ card 11 S = 3) : N 0 = 0 := by
  by_contra hne
  rcases hall 0 (Nat.two_pow_pos 11) hne with h | h
  · exact (Nat.two_pow_pos l).ne' h.symm
  · have hz : card 11 0 = 0 := by unfold card; simp
    omega

/-- with only one linear term below the top level, every vertex other than `l` is cubic -/
lemma cubicAt_of_one_linear {N : ℕ → ℤ} {l : ℕ}
    (hall : ∀ S, S < 2 ^ 11 → N S ≠ 0 → S = 2 ^ l ∨ card 11 S = 3)
    {v : ℕ} (hvl : v ≠ l) : CubicAt 11 N v := by
  intro S hS hN hb
  rcases hall S hS hN with rfl | h3
  · exact absurd (by
      by_contra hne
      rw [Nat.testBit_two_pow_of_ne (Ne.symm hne)] at hb
      exact Bool.false_ne_true hb : v = l) hvl
  · exact h3

/-- a triangle in the link of a cubic mass-4 vertex is impossible -/
lemma tri_link_absurd {N : ℕ → ℤ} (hsol : IsSol 11 N) {w a b c : ℕ}
    (hw : w < 11) (ha : a < 11) (hb : b < 11) (hc : c < 11)
    (hcub : CubicAt 11 N w) (h4 : mass 11 N w = 4)
    (haw : a ≠ w) (hbw : b ≠ w) (hcw : c ≠ w) (hbc : b ≠ c)
    (F1 : N (tri w a b) ≠ 0) (F2 : N (tri w a c) ≠ 0) (F3 : N (tri w b c) ≠ 0) : False :=
  no_triangle_at' hsol hcub hw ha hb hc h4 haw hbw hcw hbc F1 F2 F3

/-- **The common sixth vertex.**  If `o` carries the three faces of a triangle `a b c` and
`a`, `b` are cubic mass-4 vertices, then the 4-cycle links at `a` and at `b` are completed by
one and the same sixth vertex `w`, which then carries the whole triangle `a b c`. -/
lemma common_sixth {N : ℕ → ℤ} (hsol : IsSol 11 N) {o a b c : ℕ}
    (ho : o < 11) (ha : a < 11) (hb : b < 11) (hc : c < 11)
    (hao : a ≠ o) (hbo : b ≠ o) (hco : c ≠ o)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h4a : mass 11 N a = 4) (h4b : mass 11 N b = 4)
    (cua : CubicAt 11 N a) (cub : CubicAt 11 N b)
    (F1 : N (tri o a b) ≠ 0) (F2 : N (tri o a c) ≠ 0) (F3 : N (tri o b c) ≠ 0) :
    ∃ w, w < 11 ∧ w ≠ o ∧ w ≠ a ∧ w ≠ b ∧ w ≠ c ∧
      N (tri w a b) ≠ 0 ∧ N (tri w a c) ≠ 0 ∧ N (tri w b c) ≠ 0 := by
  -- the link at `a` is the 4-cycle `b - o - c - wa`
  obtain ⟨wa, hwa, hwaa, hwao, hwab, hwac, La⟩ :=
    link_sixth' hsol cua ha ho hb hc h4a (Ne.symm hao) (Ne.symm hab) (Ne.symm hac) hbc
      (by rw [show tri a o b = tri o a b from tri_ext (fun _ => by omega)]; exact F1)
      (by rw [show tri a o c = tri o a c from tri_ext (fun _ => by omega)]; exact F2)
  -- the link at `b` is the 4-cycle `a - o - c - wb`
  obtain ⟨wb, hwb, hwbb, hwbo, hwba, hwbc, Lb⟩ :=
    link_sixth' hsol cub hb ho ha hc h4b (Ne.symm hbo) hab (Ne.symm hbc) hac
      (by rw [show tri b o a = tri o a b from tri_ext (fun _ => by omega)]; exact F1)
      (by rw [show tri b o c = tri o b c from tri_ext (fun _ => by omega)]; exact F3)
  have Fac : N (tri a c wa) ≠ 0 :=
    (La c wa hc hwa (Ne.symm hac) hwaa).mpr (by unfold Edge; omega)
  have Fab : N (tri a wa b) ≠ 0 :=
    (La wa b hwa hb hwaa (Ne.symm hab)).mpr (by unfold Edge; omega)
  -- the two sixth vertices agree
  have hww : wa = wb := by
    have E := (Lb a wa ha hwa hab hwab).mp
      (by rw [show tri b a wa = tri a wa b from tri_ext (fun _ => by omega)]; exact Fab)
    have k := edge_nbr hao hac (Ne.symm hwba) (Ne.symm hco) (Ne.symm hwbo)
      (Ne.symm hwbc) E
    clear * - k hao hac hwba hwao
    omega
  have Fbc : N (tri b c wa) ≠ 0 := by
    rw [hww]
    exact (Lb c wb hc hwb (Ne.symm hbc) hwbb).mpr (by unfold Edge; omega)
  exact ⟨wa, hwa, hwao, hwaa, hwab, hwac,
    by rw [show tri wa a b = tri a wa b from tri_ext (fun _ => by omega)]; exact Fab,
    by rw [show tri wa a c = tri a c wa from tri_ext (fun _ => by omega)]; exact Fac,
    by rw [show tri wa b c = tri b c wa from tri_ext (fun _ => by omega)]; exact Fbc⟩

/-- every support set at a cubic vertex `v` is `v` together with a pair -/
lemma supp_tri {n : ℕ} {N : ℕ → ℤ} {v : ℕ} (hcub : CubicAt n N v) {S : ℕ}
    (hS : S ∈ supp n N v) :
    ∃ x y, x < n ∧ y < n ∧ x ≠ v ∧ y ≠ v ∧ x ≠ y ∧ S = tri v x y := by
  obtain ⟨hlt, hb, hN⟩ := mem_supp.mp hS
  have h3 := hcub S hlt hN hb
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr, rfl⟩ := exists_tri_of_card_three hlt h3
  rcases mem_tri_iff.mp hb with rfl | rfl | rfl
  · exact ⟨q, r, hq, hr, Ne.symm hpq, Ne.symm hpr, hqr, rfl⟩
  · exact ⟨p, r, hp, hr, hpq, Ne.symm hqr, hpr, tri_ext (fun _ => by omega)⟩
  · exact ⟨p, q, hp, hq, hpr, hqr, hpq, tri_ext (fun _ => by omega)⟩

/-- the three edges of a triangle xor to zero -/
lemma pair_tri_xor {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    pair a b ^^^ pair a c ^^^ pair b c = 0 := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_xor, testBit_pair, Nat.zero_testBit]
  by_cases ha : a = j <;> by_cases hb : b = j <;> by_cases hc : c = j <;>
    simp [ha, hb, hc] <;> omega

/-- two faces `{v,x,y}`, `{v,x,z}` through the edge `{v,x}` are distinct when `y ≠ z` -/
lemma tri_ne_of {v x y z : ℕ} (hyv : y ≠ v) (hyx : y ≠ x) (hyz : y ≠ z) :
    tri v x y ≠ tri v x z := by
  intro h
  have hb : (tri v x y).testBit y = true := mem_tri_iff.mpr (Or.inr (Or.inr rfl))
  rw [h] at hb
  rcases mem_tri_iff.mp hb with h1 | h1 | h1
  exacts [hyv h1, hyx h1, hyz h1]

/-- **The common sixth vertex is `v` or `l`.**  In the one-linear-term branch, the sixth
vertex produced by `common_sixth` cannot be an ordinary cubic mass-4 vertex. -/
lemma tri_apex_common {N : ℕ → ℤ} (hsol : IsSol 11 N) {v l : ℕ}
    (hrest : ∀ w, w < 11 → w ≠ v → mass 11 N w = 4)
    (hall : ∀ S, S < 2 ^ 11 → N S ≠ 0 → S = 2 ^ l ∨ card 11 S = 3)
    {o a b c : ℕ} (ho : o < 11) (ha : a < 11) (hb : b < 11) (hc : c < 11)
    (hao : a ≠ o) (hbo : b ≠ o) (hco : c ≠ o)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hal : a ≠ l) (hbl : b ≠ l) (hav : a ≠ v) (hbv : b ≠ v)
    (F1 : N (tri o a b) ≠ 0) (F2 : N (tri o a c) ≠ 0) (F3 : N (tri o b c) ≠ 0) :
    ∃ w, w < 11 ∧ w ≠ o ∧ w ≠ a ∧ w ≠ b ∧ w ≠ c ∧
      N (tri w a b) ≠ 0 ∧ N (tri w a c) ≠ 0 ∧ N (tri w b c) ≠ 0 ∧ (w = v ∨ w = l) := by
  obtain ⟨w, hw, hwo, hwa, hwb, hwc, G1, G2, G3⟩ :=
    common_sixth hsol ho ha hb hc hao hbo hco hab hac hbc (hrest a ha hav) (hrest b hb hbv)
      (cubicAt_of_one_linear hall hal) (cubicAt_of_one_linear hall hbl) F1 F2 F3
  refine ⟨w, hw, hwo, hwa, hwb, hwc, G1, G2, G3, ?_⟩
  by_contra hcon
  push_neg at hcon
  exact tri_link_absurd hsol hw ha hb hc (cubicAt_of_one_linear hall hcon.2)
    (hrest w hw hcon.1) (Ne.symm hwa) (Ne.symm hwb) (Ne.symm hwc) hbc G1 G2 G3

/-- a triple containing a vertex `x` that the other triple misses -/
lemma tri_ne_bit {x u1 u2 u3 p q r : ℕ} (hx : x = u1 ∨ x = u2 ∨ x = u3)
    (h1 : x ≠ p) (h2 : x ≠ q) (h3 : x ≠ r) : tri u1 u2 u3 ≠ tri p q r := by
  intro h
  have hb : (tri u1 u2 u3).testBit x = true := mem_tri_iff.mpr hx
  rw [h] at hb
  rcases mem_tri_iff.mp hb with k | k | k
  exacts [h1 k, h2 k, h3 k]

/-- Two faces `{v,u,s}` and `{v,u,t}` at a vertex `u` whose link is the 4-cycle `b-l-c-v`
force `{s,t} = {b,c}`: `s` and `t` are the two neighbours of `v` on that cycle. -/
lemma link_nbrs_of_v {N : ℕ → ℤ} {v l u b c : ℕ} (hv : v < 11)
    (hbl : b ≠ l) (hbc : b ≠ c) (hbv : b ≠ v) (hlc : l ≠ c) (hlv : l ≠ v) (hcv : c ≠ v)
    (La : ∀ p q, p < 11 → q < 11 → p ≠ u → q ≠ u → (N (tri u p q) ≠ 0 ↔ Edge b l c v p q))
    {s t : ℕ} (hs : s < 11) (ht : t < 11) (hsu : s ≠ u) (htu : t ≠ u) (hvu : v ≠ u)
    (hst : s ≠ t)
    (F1 : N (tri v u s) ≠ 0) (F2 : N (tri v u t) ≠ 0) : pair s t = pair b c := by
  have E1 : Edge b l c v v s := (La v s hv hs hvu hsu).mp
    (by rw [show tri u v s = tri v u s from tri_ext (fun _ => by omega)]; exact F1)
  have E2 : Edge b l c v v t := (La v t hv ht hvu htu).mp
    (by rw [show tri u v t = tri v u t from tri_ext (fun _ => by omega)]; exact F2)
  have k1 := edge_nbr hbl hbc hbv hlc hlv hcv E1
  have k2 := edge_nbr hbl hbc hbv hlc hlv hcv E2
  rw [pair_eq_iff]
  clear * - k1 k2 hst hbl hbc hbv hlc hlv hcv
  omega

set_option maxHeartbeats 1000000 in
/-- **The linear term sits at the mass-6 vertex.**  In the one-linear-term branch of
`δ = 2` the linear vertex `l` cannot be one of the ten mass-4 vertices. -/
theorem eleven_delta_two_lin_four {N : ℕ → ℤ} (hsol : IsSol 11 N) {v : ℕ} (hv : v < 11)
    (h6 : mass 11 N v = 6) (hrest : ∀ w, w < 11 → w ≠ v → mass 11 N w = 4)
    {l : ℕ} (hl : l < 11) (hlv : l ≠ v) (hlin : N (2 ^ l) ≠ 0)
    (hall : ∀ S, S < 2 ^ 11 → N S ≠ 0 → S = 2 ^ l ∨ card 11 S = 3) : False := by
  have hnoquad : ∀ u w, u < 11 → w < 11 → u ≠ w → N (pair u w) = 0 :=
    fun u w hu hw huw => one_linear_no_quad hall hu hw huw
  have cubv : CubicAt 11 N v := cubicAt_of_one_linear hall (Ne.symm hlv)
  obtain ⟨a, b, c, ha, hb, hc, hal, hbl, hcl, hab, hac, hbc, H⟩ :=
    link_L4_of_linear hsol hl (hrest l hl hlv) hlin
      (fun y hy hyl => hnoquad l y hl hy (Ne.symm hyl))
  have Fab : N (tri l a b) ≠ 0 :=
    (H a b ha hb hal hbl).mpr ⟨hab, Or.inl rfl, Or.inr (Or.inl rfl)⟩
  have Fac : N (tri l a c) ≠ 0 :=
    (H a c ha hc hal hcl).mpr ⟨hac, Or.inl rfl, Or.inr (Or.inr rfl)⟩
  have Fbc : N (tri l b c) ≠ 0 :=
    (H b c hb hc hbl hcl).mpr ⟨hbc, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
  -- if `v` is a vertex of the triangle the case closes at once
  have easy : ∀ p q r : ℕ, p < 11 → q < 11 → r < 11 → p ≠ l → q ≠ l → r ≠ l →
      p ≠ q → p ≠ r → q ≠ r → p ≠ v → q ≠ v → r = v →
      N (tri l p q) ≠ 0 → N (tri l p r) ≠ 0 → N (tri l q r) ≠ 0 → False := by
    intro p q r hp hq hr hpl hql hrl hpq hpr hqr hpv hqv hrv G1 G2 G3
    obtain ⟨w, hw, hwl, hwp, hwq, hwr, -, -, -, hcase⟩ :=
      tri_apex_common hsol hrest hall hl hp hq hr hpl hql hrl hpq hpr hqr hpl hql hpv hqv
        G1 G2 G3
    rcases hcase with h | h
    · exact hwr (by omega)
    · exact hwl h
  by_cases hva : a = v
  · exact easy b c a hb hc ha hbl hcl hal hbc (Ne.symm hab) (Ne.symm hac) (by omega)
      (by omega) hva Fbc
      (by rw [show tri l b a = tri l a b from tri_ext (fun _ => by omega)]; exact Fab)
      (by rw [show tri l c a = tri l a c from tri_ext (fun _ => by omega)]; exact Fac)
  by_cases hvb : b = v
  · exact easy a c b ha hc hb hal hcl hbl hac hab (Ne.symm hbc) (by omega) (by omega) hvb Fac Fab
      (by rw [show tri l c b = tri l b c from tri_ext (fun _ => by omega)]; exact Fbc)
  by_cases hvc : c = v
  · exact easy a b c ha hb hc hal hbl hcl hab hac hbc (by omega) (by omega) hvc Fab Fac Fbc
  -- the main case: `v` is not a vertex of the triangle
  obtain ⟨w, hw, hwl, hwa, hwb, hwc, G1, G2, G3, hcase⟩ :=
    tri_apex_common hsol hrest hall hl ha hb hc hal hbl hcl hab hac hbc hal hbl hva hvb
      Fab Fac Fbc
  have hwv : w = v := hcase.resolve_right hwl
  rw [hwv] at G1 G2 G3
  -- the support at `v` consists of the triangle `abc` and three further faces
  have mab : tri v a b ∈ supp 11 N v :=
    mem_supp.mpr ⟨tri_lt hv ha hb, mem_tri_iff.mpr (Or.inl rfl), G1⟩
  have mac : tri v a c ∈ supp 11 N v :=
    mem_supp.mpr ⟨tri_lt hv ha hc, mem_tri_iff.mpr (Or.inl rfl), G2⟩
  have mbc : tri v b c ∈ supp 11 N v :=
    mem_supp.mpr ⟨tri_lt hv hb hc, mem_tri_iff.mpr (Or.inl rfl), G3⟩
  have dK1 : tri v a b ≠ tri v a c :=
    tri_ne_bit (Or.inr (Or.inr rfl)) hvb (Ne.symm hab) hbc
  have dK2 : tri v a b ≠ tri v b c :=
    tri_ne_bit (Or.inr (Or.inl rfl)) hva hab hac
  have dK3 : tri v a c ≠ tri v b c :=
    tri_ne_bit (Or.inr (Or.inl rfl)) hva hab hac
  set K : Finset ℕ := {tri v a b, tri v a c, tri v b c} with hKdef
  have hKsub : K ⊆ supp 11 N v := by
    intro S hS
    simp only [hKdef, mem_insert, mem_singleton] at hS
    rcases hS with rfl | rfl | rfl
    exacts [mab, mac, mbc]
  have hKcard : K.card = 3 := by
    rw [hKdef, card_insert_of_notMem (by simp [dK1, dK2]), card_pair dK3]
  have hBcard : (supp 11 N v \ K).card = 3 := by
    rw [card_sdiff hKsub, mass_six_card hsol hv h6, hKcard]
  obtain ⟨T4, T5, T6, d45, d46, d56, hB⟩ := card_eq_three.mp hBcard
  have hT4 : T4 ∈ supp 11 N v \ K := by rw [hB]; simp
  have hT5 : T5 ∈ supp 11 N v \ K := by rw [hB]; simp
  have hT6 : T6 ∈ supp 11 N v \ K := by rw [hB]; simp
  have notK : ∀ T, T ∈ supp 11 N v \ K →
      T ≠ tri v a b ∧ T ≠ tri v a c ∧ T ≠ tri v b c := by
    intro T hT
    have hnm := (mem_sdiff.mp hT).2
    simp only [hKdef, mem_insert, mem_singleton, not_or] at hnm
    exact hnm
  obtain ⟨n41, n42, n43⟩ := notK T4 hT4
  obtain ⟨n51, n52, n53⟩ := notK T5 hT5
  obtain ⟨n61, n62, n63⟩ := notK T6 hT6
  have hsupp : supp 11 N v = {tri v a b, tri v a c, tri v b c, T4, T5, T6} := by
    have huni := union_sdiff_of_subset hKsub
    rw [hB] at huni
    rw [← huni, hKdef]
    simp only [insert_union, singleton_union]
  obtain ⟨hxor, -⟩ := mass_six hsol hv h6 dK1 dK2 (Ne.symm n41) (Ne.symm n51) (Ne.symm n61)
    dK3 (Ne.symm n42) (Ne.symm n52) (Ne.symm n62) (Ne.symm n43) (Ne.symm n53) (Ne.symm n63)
    d45 d46 d56 hsupp
  obtain ⟨x4, y4, hx4, hy4, hx4v, hy4v, hx4y4, e4⟩ := supp_tri cubv (mem_sdiff.mp hT4).1
  obtain ⟨x5, y5, hx5, hy5, hx5v, hy5v, hx5y5, e5⟩ := supp_tri cubv (mem_sdiff.mp hT5).1
  obtain ⟨x6, y6, hx6, hy6, hx6v, hy6v, hx6y6, e6⟩ := supp_tri cubv (mem_sdiff.mp hT6).1
  have hpxor : pair x4 y4 ^^^ pair x5 y5 ^^^ pair x6 y6 = 0 := by
    rw [e4, e5, e6, ← pair_xor_two_pow hva hvb, ← pair_xor_two_pow hva hvc,
      ← pair_xor_two_pow hvb hvc, ← pair_xor_two_pow hx4v hy4v,
      ← pair_xor_two_pow hx5v hy5v, ← pair_xor_two_pow hx6v hy6v,
      xor_two_pow_cancel6, pair_tri_xor hab hac hbc] at hxor
    simpa using hxor
  have dp45 : pair x4 y4 ≠ pair x5 y5 := by
    intro h
    exact d45 (by rw [e4, e5, ← pair_xor_two_pow hx4v hy4v,
      ← pair_xor_two_pow hx5v hy5v, h])
  have dp46 : pair x4 y4 ≠ pair x6 y6 := by
    intro h
    exact d46 (by rw [e4, e6, ← pair_xor_two_pow hx4v hy4v,
      ← pair_xor_two_pow hx6v hy6v, h])
  obtain ⟨x, y, z, hxy, hxz, hyz, q4, q5, q6⟩ :=
    three_pairs_triangle hx4y4 hx5y5 hx6y6 dp45 dp46 hpxor
  have mem4 := pair_mem_of_eq q4
  have mem5 := pair_mem_of_eq q5
  have mem6 := pair_mem_of_eq q6
  have hxlt : x < 11 := by omega
  have hylt : y < 11 := by omega
  have hzlt : z < 11 := by omega
  have hxv : x ≠ v := by omega
  have hyv : y ≠ v := by omega
  have hzv : z ≠ v := by omega
  have E4 : T4 = tri v x y := by
    rw [e4, ← pair_xor_two_pow hx4v hy4v, q4, pair_xor_two_pow hxv hyv]
  have E5 : T5 = tri v x z := by
    rw [e5, ← pair_xor_two_pow hx5v hy5v, q5, pair_xor_two_pow hxv hzv]
  have E6 : T6 = tri v y z := by
    rw [e6, ← pair_xor_two_pow hx6v hy6v, q6, pair_xor_two_pow hyv hzv]
  have N4 : N (tri v x y) ≠ 0 := by rw [← E4]; exact (mem_supp.mp (mem_sdiff.mp hT4).1).2.2
  have N5 : N (tri v x z) ≠ 0 := by rw [← E5]; exact (mem_supp.mp (mem_sdiff.mp hT5).1).2.2
  have N6 : N (tri v y z) ≠ 0 := by rw [← E6]; exact (mem_supp.mp (mem_sdiff.mp hT6).1).2.2
  -- the links of `a`, `b`, `c` are the 4-cycles `b-l-c-v`, `a-l-c-v`, `a-l-b-v`
  have linkat : ∀ u p q : ℕ, u < 11 → p < 11 → q < 11 → u ≠ l → p ≠ l → q ≠ l →
      u ≠ v → p ≠ v → q ≠ v → u ≠ p → u ≠ q → p ≠ q →
      N (tri l u p) ≠ 0 → N (tri l u q) ≠ 0 → N (tri v u p) ≠ 0 → N (tri v u q) ≠ 0 →
      (∀ r t, r < 11 → t < 11 → r ≠ u → t ≠ u →
        (N (tri u r t) ≠ 0 ↔ Edge p l q v r t)) := by
    intro u p q hu hp hq hul hpl hql huv hpv hqv hup huq hpq K1 K2 K3 K4
    obtain ⟨e, he, hea, hel, hep, heq, Lu⟩ :=
      link_sixth' hsol (cubicAt_of_one_linear hall hul) hu hl hp hq (hrest u hu huv)
        (Ne.symm hul) (Ne.symm hup) (Ne.symm huq) hpq
        (by rw [show tri u l p = tri l u p from tri_ext (fun _ => by omega)]; exact K1)
        (by rw [show tri u l q = tri l u q from tri_ext (fun _ => by omega)]; exact K2)
    have Ev : Edge p l q e v p := (Lu v p hv hp (Ne.symm huv) (Ne.symm hup)).mp
      (by rw [show tri u v p = tri v u p from tri_ext (fun _ => by omega)]; exact K3)
    have hev : e = v := by
      have hm := edge_mem Ev
      clear * - hm hpv hql hqv hlv
      omega
    rw [← hev]
    exact Lu
  have La := linkat a b c ha hb hc hal hbl hcl hva hvb hvc hab hac hbc Fab Fac G1 G2
  have Lb := linkat b a c hb ha hc hbl hal hcl hvb hva hvc (Ne.symm hab) hbc hac
    (by rw [show tri l b a = tri l a b from tri_ext (fun _ => by omega)]; exact Fab) Fbc
    (by rw [show tri v b a = tri v a b from tri_ext (fun _ => by omega)]; exact G1) G3
  have Lc := linkat c a b hc ha hb hcl hal hbl hvc hva hvb (Ne.symm hac) (Ne.symm hbc) hab
    (by rw [show tri l c a = tri l a c from tri_ext (fun _ => by omega)]; exact Fac)
    (by rw [show tri l c b = tri l b c from tri_ext (fun _ => by omega)]; exact Fbc)
    (by rw [show tri v c a = tri v a c from tri_ext (fun _ => by omega)]; exact G2)
    (by rw [show tri v c b = tri v b c from tri_ext (fun _ => by omega)]; exact G3)
  -- no vertex of the second triangle lies on the first
  have pair_tri : ∀ p q p' q' : ℕ, p ≠ v → q ≠ v → p' ≠ v → q' ≠ v →
      pair p q = pair p' q' → tri v p q = tri v p' q' := by
    intro p q p' q' h1 h2 h3 h4 hp
    rw [← pair_xor_two_pow h1 h2, ← pair_xor_two_pow h3 h4, hp]
  have clash : ∀ u p q : ℕ, (u = a ∨ u = b ∨ u = c) → p < 11 → q < 11 → p ≠ v → q ≠ v →
      p ≠ q → p ≠ u → q ≠ u → N (tri v u p) ≠ 0 → N (tri v u q) ≠ 0 →
      tri v p q = tri v a b ∨ tri v p q = tri v a c ∨ tri v p q = tri v b c := by
    intro u p q hu hp hq hpv hqv hpq hpu hqu K1 K2
    rcases hu with rfl | rfl | rfl
    · exact Or.inr (Or.inr (pair_tri p q b c hpv hqv hvb hvc
        (link_nbrs_of_v hv hbl hbc hvb (fun h => hcl h.symm) hlv hvc La hp hq hpu hqu
          (Ne.symm hva) hpq K1 K2)))
    · exact Or.inr (Or.inl (pair_tri p q a c hpv hqv hva hvc
        (link_nbrs_of_v hv hal hac hva (fun h => hcl h.symm) hlv hvc Lb hp hq hpu hqu
          (Ne.symm hvb) hpq K1 K2)))
    · exact Or.inl (pair_tri p q a b hpv hqv hva hvb
        (link_nbrs_of_v hv hal hab hva (fun h => hbl h.symm) hlv hvb Lc hp hq hpu hqu
          (Ne.symm hvc) hpq K1 K2))
  have hxabc : ¬ (x = a ∨ x = b ∨ x = c) := by
    intro hx
    rcases clash x y z hx hylt hzlt hyv hzv hyz (Ne.symm hxy) (Ne.symm hxz) N4 N5 with
      k | k | k
    exacts [n61 (E6.trans k), n62 (E6.trans k), n63 (E6.trans k)]
  have hyabc : ¬ (y = a ∨ y = b ∨ y = c) := by
    intro hy
    have K1 : N (tri v y x) ≠ 0 := by
      rw [show tri v y x = tri v x y from tri_ext (fun _ => by omega)]; exact N4
    rcases clash y x z hy hxlt hzlt hxv hzv hxz hxy (Ne.symm hyz) K1 N6 with k | k | k
    exacts [n51 (E5.trans k), n52 (E5.trans k), n53 (E5.trans k)]
  have hzabc : ¬ (z = a ∨ z = b ∨ z = c) := by
    intro hz
    have K1 : N (tri v z x) ≠ 0 := by
      rw [show tri v z x = tri v x z from tri_ext (fun _ => by omega)]; exact N5
    have K2 : N (tri v z y) ≠ 0 := by
      rw [show tri v z y = tri v y z from tri_ext (fun _ => by omega)]; exact N6
    rcases clash z x y hz hxlt hylt hxv hyv hxy hxz hyz K1 K2 with k | k | k
    exacts [n41 (E4.trans k), n42 (E4.trans k), n43 (E4.trans k)]
  -- and none of them is `l`
  have hnotl : ∀ u p : ℕ, u < 11 → p < 11 → u ≠ v → p ≠ v → u ≠ p →
      N (tri v u p) ≠ 0 → u ≠ l := by
    intro u p hu hp huv hpv hup K1 hul
    subst hul
    have hmem := (H v p hv hp (Ne.symm hlv) (Ne.symm hup)).mp
      (by rw [show tri u v p = tri v u p from tri_ext (fun _ => by omega)]; exact K1)
    have hvabc := hmem.2.1
    clear * - hvabc hva hvb hvc
    omega
  have hxl : x ≠ l := hnotl x y hxlt hylt hxv hyv hxy N4
  have hyl : y ≠ l := hnotl y x hylt hxlt hyv hxv (Ne.symm hxy)
    (by rw [show tri v y x = tri v x y from tri_ext (fun _ => by omega)]; exact N4)
  -- the second triangle closes on `l`, which is impossible
  obtain ⟨w2, hw2, hw2v, hw2x, hw2y, hw2z, P1, P2, P3, hcase2⟩ :=
    tri_apex_common hsol hrest hall hv hxlt hylt hzlt hxv hyv hzv hxy hxz hyz hxl hyl
      hxv hyv N4 N5 N6
  have hw2l : w2 = l := by
    rcases hcase2 with h | h
    · exact absurd h hw2v
    · exact h
  rw [hw2l] at P1
  have hfin := (H x y hxlt hylt hxl hyl).mp P1
  exact hxabc hfin.2.1

/-! ## The "one linear term" branch: the linear term at the mass-6 vertex -/

/-- a bitmask below `2 ^ n` with three bits, one of which is `v`, is `v` plus a pair -/
lemma tri_of_bit {n S v : ℕ} (hlt : S < 2 ^ n) (hb : S.testBit v = true)
    (h3 : card n S = 3) :
    ∃ x y, x < n ∧ y < n ∧ x ≠ v ∧ y ≠ v ∧ x ≠ y ∧ S = tri v x y := by
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr, rfl⟩ := exists_tri_of_card_three hlt h3
  rcases mem_tri_iff.mp hb with rfl | rfl | rfl
  · exact ⟨q, r, hq, hr, Ne.symm hpq, Ne.symm hpr, hqr, rfl⟩
  · exact ⟨p, r, hp, hr, hpq, Ne.symm hqr, hpr, tri_ext (fun _ => by omega)⟩
  · exact ⟨p, q, hp, hq, hpr, hqr, hpq, tri_ext (fun _ => by omega)⟩

/-- a power of two is never a triple -/
lemma two_pow_ne_tri {v x y : ℕ} (hx : x ≠ v) : (2 : ℕ) ^ v ≠ tri v x y := by
  intro h
  have hb : ((2 : ℕ) ^ v).testBit x = false := by
    rw [Nat.testBit_two_pow]
    simp only [decide_eq_false_iff_not]
    omega
  rw [h, mem_tri_iff.mpr (Or.inr (Or.inl rfl))] at hb
  exact Bool.noConfusion hb

/-- **Degree two in the link of `v`.**  A cubic mass-4 vertex `u` that carries one face
`{v,u,p}` carries exactly one other face `{v,u,t}`. -/
lemma other_nbr {N : ℕ → ℤ} (hsol : IsSol 11 N) {v u : ℕ} (hv : v < 11) (hu : u < 11)
    (hvu : v ≠ u) (hcub : CubicAt 11 N u) (h4 : mass 11 N u = 4)
    {p0 : ℕ} (hp0 : p0 < 11) (hp0u : p0 ≠ u) (F : N (tri v u p0) ≠ 0) :
    ∃ t, t < 11 ∧ t ≠ u ∧ t ≠ v ∧ t ≠ p0 ∧ N (tri v u t) ≠ 0 ∧
      ∀ r, r < 11 → r ≠ u → N (tri v u r) ≠ 0 → r = p0 ∨ r = t := by
  obtain ⟨p, q, r, s, hC, hL⟩ := link_struct' hsol hcub hu h4
  obtain ⟨hp, hq, hr, hs, hpu, hqu, hru, hsu, e12, e13, e14, e23, e24, e34⟩ := hC
  have gen : ∀ P Q R S : ℕ, P ≠ Q → P ≠ R → P ≠ S → Q ≠ R → Q ≠ S → R ≠ S →
      Q < 11 → S < 11 → Q ≠ u → S ≠ u → v = P →
      (∀ x y, x < 11 → y < 11 → x ≠ u → y ≠ u → (N (tri u x y) ≠ 0 ↔ Edge P Q R S x y)) →
      ∃ m n, m < 11 ∧ n < 11 ∧ m ≠ n ∧ m ≠ u ∧ n ≠ u ∧ m ≠ v ∧ n ≠ v ∧
        N (tri v u m) ≠ 0 ∧ N (tri v u n) ≠ 0 ∧
        ∀ z, z < 11 → z ≠ u → N (tri v u z) ≠ 0 → z = m ∨ z = n := by
    intro P Q R S f12 f13 f14 f23 f24 f34 hQ hS hQu hSu hvP hLL
    have hPlt : P < 11 := hvP ▸ hv
    have hPu : P ≠ u := hvP ▸ hvu
    refine ⟨Q, S, hQ, hS, f24, hQu, hSu, by omega, by omega, ?_, ?_, ?_⟩
    · rw [hvP, show tri P u Q = tri u P Q from tri_ext (fun _ => by omega)]
      exact (hLL P Q hPlt hQ hPu hQu).mpr (by unfold Edge; omega)
    · rw [hvP, show tri P u S = tri u P S from tri_ext (fun _ => by omega)]
      exact (hLL P S hPlt hS hPu hSu).mpr (by unfold Edge; omega)
    · intro z hz hzu Fz
      have Ez : Edge P Q R S P z := (hLL P z hPlt hz hPu hzu).mp
        (by rw [show tri u P z = tri v u z from tri_ext (fun _ => by omega)]; exact Fz)
      have k := edge_nbr f12 f13 f14 f23 f24 f34 Ez
      clear * - k f12 f13 f14
      omega
  have E0 : Edge p q r s v p0 := (hL v p0 hv hp0 hvu hp0u).mp
    (by rw [show tri u v p0 = tri v u p0 from tri_ext (fun _ => by omega)]; exact F)
  have hmain : ∃ m n, m < 11 ∧ n < 11 ∧ m ≠ n ∧ m ≠ u ∧ n ≠ u ∧ m ≠ v ∧ n ≠ v ∧
      N (tri v u m) ≠ 0 ∧ N (tri v u n) ≠ 0 ∧
      ∀ z, z < 11 → z ≠ u → N (tri v u z) ≠ 0 → z = m ∨ z = n := by
    rcases (edge_mem E0).1 with h | h | h | h
    · exact gen p q r s e12 e13 e14 e23 e24 e34 hq hs hqu hsu h hL
    · exact gen q r s p e23 e24 (Ne.symm e12) e34 (Ne.symm e13) (Ne.symm e14) hr hp hru hpu h
        (fun x y hx hy hxu hyu => (hL x y hx hy hxu hyu).trans edge_rot)
    · exact gen r s p q e34 (Ne.symm e13) (Ne.symm e23) (Ne.symm e14) (Ne.symm e24) e12 hs hq
        hsu hqu h
        (fun x y hx hy hxu hyu => (hL x y hx hy hxu hyu).trans (edge_rot.trans edge_rot))
    · exact gen s p q r (Ne.symm e14) (Ne.symm e24) (Ne.symm e34) e12 e13 e23 hp hr hpu hru h
        (fun x y hx hy hxu hyu =>
          (hL x y hx hy hxu hyu).trans (edge_rot.trans (edge_rot.trans edge_rot)))
  obtain ⟨m, n, hm, hn, hmn, hmu, hnu, hmv, hnv, Fm, Fn, U⟩ := hmain
  rcases U p0 hp0 hp0u F with rfl | rfl
  · exact ⟨n, hn, hnu, hnv, Ne.symm hmn, Fn, U⟩
  · exact ⟨m, hm, hmu, hmv, hmn, Fm, fun z hz hzu Fz => (U z hz hzu Fz).symm⟩

/-- a degenerate triple is a pair -/
lemma tri_degen (x y : ℕ) : tri x y x = pair x y := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [testBit_tri, testBit_pair]
  by_cases h1 : x = j <;> by_cases h2 : y = j <;> simp [h1, h2]

set_option maxHeartbeats 1000000 in
/-- **The linear term cannot sit at the mass-6 vertex either.**  Its link would be `∅`
together with five pairs of even degree, i.e. a 5-cycle, and completing the 4-cycle links
around that 5-cycle produces a mass-4 vertex carrying five faces. -/
theorem eleven_delta_two_lin_six {N : ℕ → ℤ} (hsol : IsSol 11 N) {v : ℕ} (hv : v < 11)
    (h6 : mass 11 N v = 6) (hrest : ∀ w, w < 11 → w ≠ v → mass 11 N w = 4)
    (hlin : N (2 ^ v) ≠ 0)
    (hall : ∀ S, S < 2 ^ 11 → N S ≠ 0 → S = 2 ^ v ∨ card 11 S = 3) : False := by
  have hnoquad : ∀ u w, u < 11 → w < 11 → u ≠ w → N (pair u w) = 0 :=
    fun u w hu hw huw => one_linear_no_quad hall hu hw huw
  have cub : ∀ u, u ≠ v → CubicAt 11 N u := fun u h => cubicAt_of_one_linear hall h
  have hface : ∀ T, T ∈ supp 11 N v → T ≠ 2 ^ v →
      ∃ x y, x < 11 ∧ y < 11 ∧ x ≠ v ∧ y ≠ v ∧ x ≠ y ∧ T = tri v x y := by
    intro T hT hne
    obtain ⟨hlt, hb, hN⟩ := mem_supp.mp hT
    rcases hall T hlt hN with h | h3
    · exact absurd h hne
    · exact tri_of_bit hlt hb h3
  have hmemtri : ∀ x y : ℕ, x < 11 → y < 11 → N (tri v x y) ≠ 0 →
      tri v x y ∈ supp 11 N v := fun x y hx hy hN =>
    mem_supp.mpr ⟨tri_lt hv hx hy, mem_tri_iff.mpr (Or.inl rfl), hN⟩
  have hm2v : (2 : ℕ) ^ v ∈ supp 11 N v :=
    mem_supp.mpr ⟨Nat.pow_lt_pow_right (by norm_num) hv, Nat.testBit_two_pow_self, hlin⟩
  have hcard6 := mass_six_card hsol hv h6
  have hne5 : (supp 11 N v \ ({2 ^ v} : Finset ℕ)).card = 5 := by
    rw [card_sdiff (by simpa using hm2v), hcard6, card_singleton]
  obtain ⟨T0, hT0⟩ :=
    card_pos.mp (show 0 < (supp 11 N v \ ({2 ^ v} : Finset ℕ)).card by omega)
  obtain ⟨a, b, ha, hb, hav, hbv, hab, hT0eq⟩ :=
    hface T0 (mem_sdiff.mp hT0).1 (by simpa using (mem_sdiff.mp hT0).2)
  have Fab : N (tri v a b) ≠ 0 := by
    rw [← hT0eq]; exact (mem_supp.mp (mem_sdiff.mp hT0).1).2.2
  have Fba : N (tri v b a) ≠ 0 := by
    rw [show tri v b a = tri v a b from tri_ext (fun _ => by omega)]; exact Fab
  obtain ⟨c, hc, hca, hcv, hcb, Fac, Ua⟩ :=
    other_nbr hsol hv ha (Ne.symm hav) (cub a hav) (hrest a ha hav) hb (Ne.symm hab) Fab
  obtain ⟨d, hd, hdb, hdv, hda, Fbd, Ub⟩ :=
    other_nbr hsol hv hb (Ne.symm hbv) (cub b hbv) (hrest b hb hbv) ha hab Fba
  -- the 4-cycle links at `a` and at `b` share their sixth vertex `w`
  obtain ⟨w, hw, hwa, hwv, hwb, hwc, La⟩ :=
    link_sixth' hsol (cub a hav) ha hv hb hc (hrest a ha hav) (Ne.symm hav) (Ne.symm hab)
      hca (Ne.symm hcb)
      (by rw [show tri a v b = tri v a b from tri_ext (fun _ => by omega)]; exact Fab)
      (by rw [show tri a v c = tri v a c from tri_ext (fun _ => by omega)]; exact Fac)
  obtain ⟨w', hw', hw'b, hw'v, hw'a, hw'd, Lb⟩ :=
    link_sixth' hsol (cub b hbv) hb hv ha hd (hrest b hb hbv) (Ne.symm hbv) hab hdb
      (Ne.symm hda)
      (by rw [show tri b v a = tri v b a from tri_ext (fun _ => by omega)]; exact Fba)
      (by rw [show tri b v d = tri v b d from tri_ext (fun _ => by omega)]; exact Fbd)
  have Wab0 : N (tri a w b) ≠ 0 :=
    (La w b hw hb hwa (Ne.symm hab)).mpr (by unfold Edge; omega)
  have hww : w = w' := by
    have E := (Lb a w ha hw hab hwb).mp
      (by rw [show tri b a w = tri a w b from tri_ext (fun _ => by omega)]; exact Wab0)
    have k := edge_nbr hav (Ne.symm hda) (Ne.symm hw'a) (Ne.symm hdv) (Ne.symm hw'v)
      (Ne.symm hw'd) E
    clear * - k hav hda hw'a hwv
    omega
  have Wab : N (tri w a b) ≠ 0 := by
    rw [show tri w a b = tri a w b from tri_ext (fun _ => by omega)]; exact Wab0
  have Wac : N (tri w a c) ≠ 0 := by
    rw [show tri w a c = tri a c w from tri_ext (fun _ => by omega)]
    exact (La c w hc hw hca hwa).mpr (by unfold Edge; omega)
  have Wbd : N (tri w b d) ≠ 0 := by
    rw [show tri w b d = tri b d w from tri_ext (fun _ => by omega), hww]
    exact (Lb d w' hd hw' hdb hw'b).mpr (by unfold Edge; omega)
  by_cases hcd : c = d
  · exact tri_link_absurd hsol hw ha hb hc (cub w hwv) (hrest w hw hwv) (Ne.symm hwa)
      (Ne.symm hwb) (Ne.symm hwc) (Ne.symm hcb) Wab Wac (by rw [hcd]; exact Wbd)
  have hwd : w ≠ d := by
    intro h
    rw [h] at Wbd
    exact Wbd (by rw [tri_degen]; exact hnoquad d b hd hb hdb)
  -- the link at `w` is the 4-cycle `b - a - c - d`
  have Lw := link_of_three_faces' hsol (cub w hwv) hw ha hb hc hd (hrest w hw hwv)
    (Ne.symm hwa) (Ne.symm hwb) (Ne.symm hwc) (Ne.symm hwd) (Ne.symm hcb) hab hda
    Wab Wac Wbd
  have Wcd : N (tri w c d) ≠ 0 :=
    (Lw c d hc hd (Ne.symm hwc) (Ne.symm hwd)).mpr (by unfold Edge; omega)
  -- hence `c` is adjacent to `d` in the link of `v`
  have Fca : N (tri v c a) ≠ 0 := by
    rw [show tri v c a = tri v a c from tri_ext (fun _ => by omega)]; exact Fac
  obtain ⟨f, hf, hfc, hfv, hfa, Fcf, Uc0⟩ :=
    other_nbr hsol hv hc (Ne.symm hcv) (cub c hcv) (hrest c hc hcv) ha (Ne.symm hca) Fca
  obtain ⟨w2, hw2, hw2c, hw2v, hw2a, hw2f, Lc⟩ :=
    link_sixth' hsol (cub c hcv) hc hv ha hf (hrest c hc hcv) (Ne.symm hcv) (Ne.symm hca)
      hfc (Ne.symm hfa)
      (by rw [show tri c v a = tri v c a from tri_ext (fun _ => by omega)]; exact Fca)
      (by rw [show tri c v f = tri v c f from tri_ext (fun _ => by omega)]; exact Fcf)
  have Wca : N (tri c a w) ≠ 0 := by
    rw [show tri c a w = tri w a c from tri_ext (fun _ => by omega)]; exact Wac
  have hww2 : w = w2 := by
    have E := (Lc a w ha hw (Ne.symm hca) hwc).mp Wca
    have k := edge_nbr hav (Ne.symm hfa) (Ne.symm hw2a) (Ne.symm hfv) (Ne.symm hw2v)
      (Ne.symm hw2f) E
    clear * - k hav hfa hw2a hwv
    omega
  have hdf : d = f := by
    have E : Edge a v f w2 d w2 := (Lc d w2 hd hw2 (fun h => hcd h.symm) hw2c).mp
      (by rw [← hww2, show tri c d w = tri w c d from tri_ext (fun _ => by omega)]; exact Wcd)
    have k := edge_nbr hav (Ne.symm hfa) (Ne.symm hw2a) (Ne.symm hfv) (Ne.symm hw2v)
      (Ne.symm hw2f) E
    clear * - k hda hdv hwd hww2
    omega
  have Fcd : N (tri v c d) ≠ 0 := by rw [hdf]; exact Fcf
  have Uc : ∀ r, r < 11 → r ≠ c → N (tri v c r) ≠ 0 → r = a ∨ r = d := by
    intro r hr hrc Fr
    rcases Uc0 r hr hrc Fr with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have Fdb : N (tri v d b) ≠ 0 := by
    rw [show tri v d b = tri v b d from tri_ext (fun _ => by omega)]; exact Fbd
  have Fdc : N (tri v d c) ≠ 0 := by
    rw [show tri v d c = tri v c d from tri_ext (fun _ => by omega)]; exact Fcd
  obtain ⟨g, hg, hgd, hgv, hgb, Fdg, Ud0⟩ :=
    other_nbr hsol hv hd (Ne.symm hdv) (cub d hdv) (hrest d hd hdv) hb (Ne.symm hdb) Fdb
  have hgc : g = c := by
    rcases Ud0 c hc hcd Fdc with h | h
    · exact absurd h hcb
    · exact h.symm
  have Ud : ∀ r, r < 11 → r ≠ d → N (tri v d r) ≠ 0 → r = b ∨ r = c := by
    intro r hr hrd Fr
    rcases Ud0 r hr hrd Fr with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  -- the four faces of `v` on `{a,b,c,d}`
  have dA : tri v a b ≠ tri v a c :=
    tri_ne_bit (Or.inr (Or.inr rfl)) hbv (Ne.symm hab) (Ne.symm hcb)
  have dB : tri v a b ≠ tri v b d :=
    tri_ne_bit (Or.inr (Or.inl rfl)) hav hab (Ne.symm hda)
  have dC : tri v a b ≠ tri v c d :=
    tri_ne_bit (Or.inr (Or.inl rfl)) hav (Ne.symm hca) (Ne.symm hda)
  have dD : tri v a c ≠ tri v b d :=
    tri_ne_bit (Or.inr (Or.inl rfl)) hav hab (Ne.symm hda)
  have dE : tri v a c ≠ tri v c d :=
    tri_ne_bit (Or.inr (Or.inl rfl)) hav (Ne.symm hca) (Ne.symm hda)
  have dF : tri v b d ≠ tri v c d :=
    tri_ne_bit (Or.inr (Or.inl rfl)) hbv (Ne.symm hcb) (Ne.symm hdb)
  set M : Finset ℕ := {2 ^ v, tri v a b, tri v a c, tri v b d, tri v c d} with hMdef
  have hMcard : M.card = 5 := by
    rw [hMdef,
      card_insert_of_notMem (by
        simp only [mem_insert, mem_singleton, not_or]
        exact ⟨two_pow_ne_tri hav, two_pow_ne_tri hav, two_pow_ne_tri hbv,
          two_pow_ne_tri hcv⟩),
      card_insert_of_notMem (by simp [dA, dB, dC]),
      card_insert_of_notMem (by simp [dD, dE]), card_insert_of_notMem (by simp [dF]),
      card_singleton]
  have hMsub : M ⊆ supp 11 N v := by
    intro S hS
    simp only [hMdef, mem_insert, mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl
    exacts [hm2v, hmemtri a b ha hb Fab, hmemtri a c ha hc Fac, hmemtri b d hb hd Fbd,
      hmemtri c d hc hd Fcd]
  have hrest1 : (supp 11 N v \ M).card = 1 := by
    rw [card_sdiff hMsub, hcard6, hMcard]
  obtain ⟨T5, hT5⟩ := card_eq_one.mp hrest1
  have hT5mem : T5 ∈ supp 11 N v \ M := by rw [hT5]; simp
  have hT5notM : T5 ∉ M := (mem_sdiff.mp hT5mem).2
  have hsupp : supp 11 N v = M ∪ {T5} := by
    have huni := union_sdiff_of_subset hMsub
    rw [hT5] at huni
    exact huni.symm
  obtain ⟨s, t, hs, ht, hsv, htv, hst, hT5eq⟩ :=
    hface T5 (mem_sdiff.mp hT5mem).1 (by
      intro h
      exact hT5notM (by rw [h, hMdef]; simp))
  have Fst : N (tri v s t) ≠ 0 := by
    rw [← hT5eq]; exact (mem_supp.mp (mem_sdiff.mp hT5mem).1).2.2
  -- neither endpoint of the fifth face lies on `{a,b,c,d}`
  have hfree : ∀ p q : ℕ, p < 11 → q < 11 → p ≠ q → N (tri v p q) ≠ 0 →
      tri v p q = T5 → ¬ (p = a ∨ p = b ∨ p = c ∨ p = d) := by
    intro p q hp hq hpq Fpq hEq hmem
    apply hT5notM
    rw [← hEq]
    rcases hmem with rfl | rfl | rfl | rfl
    · rcases Ua q hq (Ne.symm hpq) Fpq with rfl | rfl
      · rw [hMdef]; simp
      · rw [hMdef]; simp
    · rcases Ub q hq (Ne.symm hpq) Fpq with rfl | rfl
      · rw [show tri v p q = tri v q p from tri_ext (fun _ => by omega), hMdef]; simp
      · rw [hMdef]; simp
    · rcases Uc q hq (Ne.symm hpq) Fpq with rfl | rfl
      · rw [show tri v p q = tri v q p from tri_ext (fun _ => by omega), hMdef]; simp
      · rw [hMdef]; simp
    · rcases Ud q hq (Ne.symm hpq) Fpq with rfl | rfl
      · rw [show tri v p q = tri v q p from tri_ext (fun _ => by omega), hMdef]; simp
      · rw [show tri v p q = tri v q p from tri_ext (fun _ => by omega), hMdef]; simp
  have hsfree := hfree s t hs ht hst Fst hT5eq.symm
  have htfree := hfree t s ht hs (Ne.symm hst) (by
    rw [show tri v t s = tri v s t from tri_ext (fun _ => by omega)]; exact Fst)
    (by rw [show tri v t s = tri v s t from tri_ext (fun _ => by omega)]; exact hT5eq.symm)
  -- but then `s` has only one neighbour in the link of `v`
  obtain ⟨g2, hg2, hg2s, hg2v, hg2t, Fsg2, -⟩ :=
    other_nbr hsol hv hs (Ne.symm hsv) (cub s hsv) (hrest s hs hsv) ht (Ne.symm hst) Fst
  have hmem2 : tri v s g2 ∈ M ∪ {T5} := by have hx := hmemtri s g2 hs hg2 Fsg2; rwa [hsupp] at hx
  simp only [hMdef, mem_union, mem_insert, mem_singleton] at hmem2
  have hne2 : tri v s g2 ≠ T5 := by
    rw [hT5eq]
    exact tri_ne_bit (Or.inr (Or.inr rfl)) hg2v hg2s hg2t
  rcases hmem2 with (h | h | h | h | h) | h
  · exact two_pow_ne_tri hsv h.symm
  · exact (tri_ne_bit (Or.inr (Or.inl rfl)) hsv (by omega) (by omega) :
      tri v s g2 ≠ tri v a b) h
  · exact (tri_ne_bit (Or.inr (Or.inl rfl)) hsv (by omega) (by omega) :
      tri v s g2 ≠ tri v a c) h
  · exact (tri_ne_bit (Or.inr (Or.inl rfl)) hsv (by omega) (by omega) :
      tri v s g2 ≠ tri v b d) h
  · exact (tri_ne_bit (Or.inr (Or.inl rfl)) hsv (by omega) (by omega) :
      tri v s g2 ≠ tri v c d) h
  · exact hne2 h

/-! ## The case `δ = 2` -/

/-- **The case `δ = 2` of F(11) is impossible.**  An 11-variable solution cannot have one
vertex of mass 6 and ten vertices of mass 4. -/
theorem eleven_delta_two {N : ℕ → ℤ} (hsol : IsSol 11 N) {v : ℕ} (hv : v < 11)
    (h6 : mass 11 N v = 6) (hrest : ∀ w, w < 11 → w ≠ v → mass 11 N w = 4) : False := by
  have hD := delta_two_weight hsol hv h6 hrest
  by_cases hlow : ∃ S, S < 2 ^ 11 ∧ N S ≠ 0 ∧ card 11 S ≤ 1
  · obtain ⟨L, hL, hLN, hLc⟩ := hlow
    obtain ⟨hc1, -, hother⟩ := delta_two_linear hsol hD hL hLN hLc
    obtain ⟨l, hl, rfl⟩ := exists_two_pow_of_card_one hL hc1
    have hall : ∀ S, S < 2 ^ 11 → N S ≠ 0 → S = 2 ^ l ∨ card 11 S = 3 := by
      intro S hS hN
      by_cases h : S = 2 ^ l
      · exact Or.inl h
      · exact Or.inr (hother S hS hN h)
    by_cases hlv : l = v
    · subst hlv
      exact eleven_delta_two_lin_six hsol hv h6 hrest hLN hall
    · exact eleven_delta_two_lin_four hsol hv h6 hrest hl hlv hLN hall
  · push_neg at hlow
    exact eleven_delta_two_quad hsol hv h6 hrest
      (fun S hS hN => by have := hlow S hS hN; omega)

end R3
