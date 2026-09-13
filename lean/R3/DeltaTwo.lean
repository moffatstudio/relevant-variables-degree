import R3.LinkSix
import R3.Final
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

lemma card_quad_eq {T1 T2 T3 T4 : ℕ} (d12 : T1 ≠ T2) (d13 : T1 ≠ T3) (d14 : T1 ≠ T4)
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
    rw [card_quad_eq d12 d13 d14 d23 d24 d34]
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

lemma pair_lt {n p q : ℕ} (hp : p < n) (hq : q < n) (hpq : p ≠ q) : pair p q < 2 ^ n := by
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
  have hQlt : pair u w < 2 ^ 11 := pair_lt hu hw huw
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
  have lua : pair u a < 2 ^ 11 := pair_lt hu ha (Ne.symm hau)
  have lub : pair u b < 2 ^ 11 := pair_lt hu hb (Ne.symm hbu)
  have lae : pair a e < 2 ^ 11 := pair_lt ha he (Ne.symm hea)
  have laf : pair a f < 2 ^ 11 := pair_lt ha hf (Ne.symm hfa)
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

end R3
