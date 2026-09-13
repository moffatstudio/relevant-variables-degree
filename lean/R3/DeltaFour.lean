import R3.Final
import R3.LinkTypes
/-!
# Case `δ = 4` of R3_equals_10.md at `n = 11`

`δ = 4` is the case in which every vertex has mass 4, so the whole of the "excess" budget
`e + δ = 48 - 4n = 4` sits on the terms of degree below three.

This file first builds the *link cover* interface: at a mass-4 vertex the link, viewed as a
four-element `Finset` of bitmasks, is literally one of the four explicit sets
L1 `{pq, qr, rs, sp}`, L2 `{∅, a, b, ab}`, L3 `{a, b, ac, bc}`, L4 `{∅, ab, bc, ac}`
(`mass_four_link_cover`).  This turns every link argument into membership in an explicit
four-element `Finset`, which `simp`/`omega` handle.
-/
namespace R3
open Finset

/-! ## `four_cover`: four distinct values inside a four-element list exhaust it -/

/-- Four *distinct* naturals, each one of `x1, x2, x3, x4`, are exactly `x1, x2, x3, x4`. -/
lemma four_cover {T1 T2 T3 T4 x1 x2 x3 x4 : ℕ}
    (d12 : T1 ≠ T2) (d13 : T1 ≠ T3) (d14 : T1 ≠ T4)
    (d23 : T2 ≠ T3) (d24 : T2 ≠ T4) (d34 : T3 ≠ T4)
    (h1 : T1 = x1 ∨ T1 = x2 ∨ T1 = x3 ∨ T1 = x4)
    (h2 : T2 = x1 ∨ T2 = x2 ∨ T2 = x3 ∨ T2 = x4)
    (h3 : T3 = x1 ∨ T3 = x2 ∨ T3 = x3 ∨ T3 = x4)
    (h4 : T4 = x1 ∨ T4 = x2 ∨ T4 = x3 ∨ T4 = x4) :
    ({T1, T2, T3, T4} : Finset ℕ) = {x1, x2, x3, x4} := by
  have hsub : ({T1, T2, T3, T4} : Finset ℕ) ⊆ {x1, x2, x3, x4} := by
    intro t ht
    simp only [mem_insert, mem_singleton] at ht ⊢
    rcases ht with rfl | rfl | rfl | rfl <;> tauto
  refine eq_of_subset_of_card_le hsub ?_
  have hcard : ({T1, T2, T3, T4} : Finset ℕ).card = 4 := by
    rw [card_insert_of_notMem (by simp [d12, d13, d14]),
      card_insert_of_notMem (by simp [d23, d24]), card_pair d34]
  rw [hcard]; exact card_quad_le _ _ _ _

/-! ## The link of a vertex as a `Finset` -/

/-- the link of `v`: the family `{S ∖ {v} : N S ≠ 0, v ∈ S}`, as a `Finset` of bitmasks -/
def link (n : ℕ) (N : ℕ → ℤ) (v : ℕ) : Finset ℕ :=
  (supp n N v).image (fun S => S ^^^ 2 ^ v)

lemma xor_two_pow_invol (S v : ℕ) : (S ^^^ 2 ^ v) ^^^ 2 ^ v = S := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

lemma mem_link {n : ℕ} {N : ℕ → ℤ} {v T : ℕ} :
    T ∈ link n N v ↔ (T ^^^ 2 ^ v) ∈ supp n N v := by
  unfold link
  rw [mem_image]
  constructor
  · rintro ⟨S, hS, rfl⟩; rwa [xor_two_pow_invol]
  · intro h; exact ⟨T ^^^ 2 ^ v, h, xor_two_pow_invol T v⟩

/-- the linear term `{v}` is present iff `∅` is in the link -/
lemma zero_mem_link {n : ℕ} {N : ℕ → ℤ} {v : ℕ} (hv : v < n) :
    (0 : ℕ) ∈ link n N v ↔ N (2 ^ v) ≠ 0 := by
  rw [mem_link, Nat.zero_xor, mem_supp]
  constructor
  · exact fun h => h.2.2
  · exact fun h => ⟨Nat.pow_lt_pow_right (by norm_num) hv, Nat.testBit_two_pow_self, h⟩

/-- the quadratic term `{v, y}` is present iff the singleton `{y}` is in the link -/
lemma two_pow_mem_link {n : ℕ} {N : ℕ → ℤ} {v y : ℕ} (hv : v < n) (hy : y < n) (hyv : y ≠ v) :
    (2 : ℕ) ^ y ∈ link n N v ↔ N (pair v y) ≠ 0 := by
  rw [mem_link, two_pow_xor_two_pow hyv, pair_comm y v, mem_supp]
  constructor
  · exact fun h => h.2.2
  · refine fun h => ⟨?_, mem_pair_iff.mpr (Or.inl rfl), h⟩
    have h1 : (2 : ℕ) ^ v < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hv
    have h2 : (2 : ℕ) ^ y < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hy
    unfold pair
    exact Nat.or_lt_two_pow h1 h2

/-- the cubic term `{v, x, y}` is present iff the pair `{x, y}` is in the link -/
lemma pair_mem_link {n : ℕ} {N : ℕ → ℤ} {v x y : ℕ} (hv : v < n) (hx : x < n) (hy : y < n)
    (hxv : x ≠ v) (hyv : y ≠ v) :
    pair x y ∈ link n N v ↔ N (tri v x y) ≠ 0 := by
  rw [mem_link, pair_xor_two_pow hxv hyv, mem_supp]
  constructor
  · exact fun h => h.2.2
  · exact fun h => ⟨tri_lt hv hx hy, mem_tri_iff.mpr (Or.inl rfl), h⟩

/-- every member of the link avoids `v` -/
lemma link_not_self {n : ℕ} {N : ℕ → ℤ} {v T : ℕ} (hT : T ∈ link n N v) :
    T.testBit v = false := by
  rw [mem_link, mem_supp] at hT
  have := hT.2.1
  rw [Nat.testBit_xor, Nat.testBit_two_pow_self] at this
  cases h : T.testBit v with
  | false => rfl
  | true => rw [h] at this; simp at this

/-- every member of the link lies below `2 ^ n` -/
lemma link_lt {n : ℕ} {N : ℕ → ℤ} {v T : ℕ} (hv : v < n) (hT : T ∈ link n N v) : T < 2 ^ n := by
  rw [mem_link, mem_supp] at hT
  have h2v : (2 : ℕ) ^ v < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hv
  have := Nat.xor_lt_two_pow hT.1 h2v
  rwa [xor_two_pow_invol] at this

/-! ## The four shapes of a mass-4 link -/

/-- **The link cover.**  At a mass-4 vertex the link is, as a `Finset`, one of the four
explicit four-element families L1..L4 of Lemma 2(a). -/
theorem mass_four_link_cover {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n)
    (h4 : mass n N v = 4) :
    (∃ p q r s, p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
        link n N v = {pair p q, pair q r, pair r s, pair s p}) ∨
    (∃ a b, a ≠ b ∧ link n N v = {0, 2 ^ a, 2 ^ b, pair a b}) ∨
    (∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ link n N v = {2 ^ a, 2 ^ b, pair a c, pair b c}) ∨
    (∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ link n N v = {0, pair a b, pair b c, pair a c}) := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs, hall, hxor, -⟩ :=
    mass_four_link hsol hv h4
  have h2v : (2 : ℕ) ^ v < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hv
  have inj : ∀ x y : ℕ, x ^^^ 2 ^ v = y ^^^ 2 ^ v → x = y := by
    intro x y h
    have := congrArg (fun z => z ^^^ 2 ^ v) h
    simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this
  have hlink : link n N v = {a ^^^ 2 ^ v, b ^^^ 2 ^ v, c ^^^ 2 ^ v, d ^^^ 2 ^ v} := by
    unfold link; rw [hs]
    simp [Finset.image_insert]
  have hb1 : a ^^^ 2 ^ v < 2 ^ n := Nat.xor_lt_two_pow (hall a (by simp)).1 h2v
  have hb2 : b ^^^ 2 ^ v < 2 ^ n := Nat.xor_lt_two_pow (hall b (by simp)).1 h2v
  have hb3 : c ^^^ 2 ^ v < 2 ^ n := Nat.xor_lt_two_pow (hall c (by simp)).1 h2v
  have hb4 : d ^^^ 2 ^ v < 2 ^ n := Nat.xor_lt_two_pow (hall d (by simp)).1 h2v
  have hc1 : card n (a ^^^ 2 ^ v) ≤ 2 := (hall a (by simp)).2.2.2.2.1
  have hc2 : card n (b ^^^ 2 ^ v) ≤ 2 := (hall b (by simp)).2.2.2.2.1
  have hc3 : card n (c ^^^ 2 ^ v) ≤ 2 := (hall c (by simp)).2.2.2.2.1
  have hc4 : card n (d ^^^ 2 ^ v) ≤ 2 := (hall d (by simp)).2.2.2.2.1
  have d12 : a ^^^ 2 ^ v ≠ b ^^^ 2 ^ v := fun h => hab (inj _ _ h)
  have d13 : a ^^^ 2 ^ v ≠ c ^^^ 2 ^ v := fun h => hac (inj _ _ h)
  have d14 : a ^^^ 2 ^ v ≠ d ^^^ 2 ^ v := fun h => had (inj _ _ h)
  have d23 : b ^^^ 2 ^ v ≠ c ^^^ 2 ^ v := fun h => hbc (inj _ _ h)
  have d24 : b ^^^ 2 ^ v ≠ d ^^^ 2 ^ v := fun h => hbd (inj _ _ h)
  have d34 : c ^^^ 2 ^ v ≠ d ^^^ 2 ^ v := fun h => hcd (inj _ _ h)
  rcases link_types hb1 hb2 hb3 hb4 hc1 hc2 hc3 hc4 d12 d13 d14 d23 d24 d34 hxor with
    ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, o1, o2, o3, o4⟩ |
    ⟨x, y, hxy, o1, o2, o3, o4⟩ |
    ⟨x, y, z, hxy, hxz, hyz, o1, o2, o3, o4⟩ |
    ⟨x, y, z, hxy, hxz, hyz, o1, o2, o3, o4⟩
  · exact Or.inl ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, by
      rw [hlink]; exact four_cover d12 d13 d14 d23 d24 d34 o1 o2 o3 o4⟩
  · exact Or.inr (Or.inl ⟨x, y, hxy, by
      rw [hlink]; exact four_cover d12 d13 d14 d23 d24 d34 o1 o2 o3 o4⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x, y, z, hxy, hxz, hyz, by
      rw [hlink]; exact four_cover d12 d13 d14 d23 d24 d34 o1 o2 o3 o4⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x, y, z, hxy, hxz, hyz, by
      rw [hlink]; exact four_cover d12 d13 d14 d23 d24 d34 o1 o2 o3 o4⟩))

/-! ## Reading the cover back as coefficients -/

lemma lt_of_testBit {n T j : ℕ} (hT : T < 2 ^ n) (hj : T.testBit j = true) : j < n := by
  by_contra hc
  push_neg at hc
  rw [testBit_eq_false_of_lt hT hc] at hj
  exact Bool.false_ne_true hj

/-- a singleton in the link is a quadratic term at `v` -/
lemma link_two_pow {n : ℕ} {N : ℕ → ℤ} {v y : ℕ} (hv : v < n) (hy : (2 : ℕ) ^ y ∈ link n N v) :
    y < n ∧ y ≠ v ∧ N (pair v y) ≠ 0 := by
  have hyn : y < n := lt_of_testBit (link_lt hv hy) Nat.testBit_two_pow_self
  have hyv : y ≠ v := by
    rintro rfl
    have h1 := link_not_self hy
    rw [Nat.testBit_two_pow_self] at h1
    simp at h1
  exact ⟨hyn, hyv, (two_pow_mem_link hv hyn hyv).mp hy⟩

/-- a pair in the link is a cubic term at `v` -/
lemma link_pair {n : ℕ} {N : ℕ → ℤ} {v x y : ℕ} (hv : v < n) (h : pair x y ∈ link n N v) :
    x < n ∧ y < n ∧ x ≠ v ∧ y ≠ v ∧ N (tri v x y) ≠ 0 := by
  have hb := link_lt hv h
  have hnb := link_not_self h
  have hxn : x < n := lt_of_testBit hb (mem_pair_iff.mpr (Or.inl rfl))
  have hyn : y < n := lt_of_testBit hb (mem_pair_iff.mpr (Or.inr rfl))
  have hxv : x ≠ v := by
    rintro rfl
    rw [mem_pair_iff.mpr (Or.inl rfl)] at hnb
    simp at hnb
  have hyv : y ≠ v := by
    rintro rfl
    rw [mem_pair_iff.mpr (Or.inr rfl)] at hnb
    simp at hnb
  exact ⟨hxn, hyn, hxv, hyv, (pair_mem_link hv hxn hyn hxv hyv).mp h⟩

/-! ## Every vertex has 0 or 2 quadratic terms -/

/-- **The quadratic graph is 2-regular.**  At a mass-4 vertex carrying one quadratic term
`{v, x}` there is a second quadratic term `{v, y}` with `y ≠ x`.  (In Lemma 2(a)'s language:
a link containing a singleton is L2 or L3, and both contain exactly two singletons.) -/
theorem quad_deg_two {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v x : ℕ} (hv : v < n)
    (hx : x < n) (hxv : x ≠ v) (h4 : mass n N v = 4) (hq : N (pair v x) ≠ 0) :
    ∃ y, y < n ∧ y ≠ v ∧ y ≠ x ∧ N (pair v y) ≠ 0 := by
  have hmem : (2 : ℕ) ^ x ∈ link n N v := (two_pow_mem_link hv hx hxv).mpr hq
  rcases mass_four_link_cover hsol hv h4 with
    ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, hL⟩ | ⟨a, b, hab, hL⟩ |
    ⟨a, b, c, hab, hac, hbc, hL⟩ | ⟨a, b, c, hab, hac, hbc, hL⟩
  · exfalso
    rw [hL] at hmem
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact pair_ne_two_pow hpq h.symm
    · exact pair_ne_two_pow hqr h.symm
    · exact pair_ne_two_pow hrs h.symm
    · exact pair_ne_two_pow (Ne.symm hps) h.symm
  · have hA : (2 : ℕ) ^ a ∈ link n N v := by rw [hL]; simp
    have hB : (2 : ℕ) ^ b ∈ link n N v := by rw [hL]; simp
    rw [hL] at hmem
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact absurd h (Nat.two_pow_pos x).ne'
    · have hxa : x = a := Nat.pow_right_injective (le_refl 2) h
      obtain ⟨hbn, hbv, hbq⟩ := link_two_pow hv hB
      exact ⟨b, hbn, hbv, by rw [hxa]; exact Ne.symm hab, hbq⟩
    · have hxb : x = b := Nat.pow_right_injective (le_refl 2) h
      obtain ⟨han, hav, haq⟩ := link_two_pow hv hA
      exact ⟨a, han, hav, by rw [hxb]; exact hab, haq⟩
    · exact absurd h.symm (pair_ne_two_pow hab)
  · have hA : (2 : ℕ) ^ a ∈ link n N v := by rw [hL]; simp
    have hB : (2 : ℕ) ^ b ∈ link n N v := by rw [hL]; simp
    rw [hL] at hmem
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · have hxa : x = a := Nat.pow_right_injective (le_refl 2) h
      obtain ⟨hbn, hbv, hbq⟩ := link_two_pow hv hB
      exact ⟨b, hbn, hbv, by rw [hxa]; exact Ne.symm hab, hbq⟩
    · have hxb : x = b := Nat.pow_right_injective (le_refl 2) h
      obtain ⟨han, hav, haq⟩ := link_two_pow hv hA
      exact ⟨a, han, hav, by rw [hxb]; exact hab, haq⟩
    · exact absurd h.symm (pair_ne_two_pow hac)
    · exact absurd h.symm (pair_ne_two_pow hbc)
  · exfalso
    rw [hL] at hmem
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact absurd h (Nat.two_pow_pos x).ne'
    · exact pair_ne_two_pow hab h.symm
    · exact pair_ne_two_pow hbc h.symm
    · exact pair_ne_two_pow hac h.symm

/-! ## The `δ` budget at `n = 11`

With every mass equal to 4 the bookkeeping identity reads `δ = 4`, where
`δ = ∑_S (3 - |S|) n_S²` is a sum of non-negative terms.  A set of size 3 contributes 0,
a quadratic 1, a linear term 2 and the constant 3, so only four terms of weight 1, or two
of weight 2, or one of weight 3 and one of weight 1, ... can be present.  `sum_dw_le` is the
upper bound, `dw_saturate` says a sub-family of total weight 4 already carries all of `δ`,
and `exists_dw_outside` produces a further low-degree term while the budget is not spent. -/

/-- the `δ`-weight of a set: `(3 - |S|) n_S²` -/
def dw (n : ℕ) (N : ℕ → ℤ) (S : ℕ) : ℤ := ((3 : ℤ) - card n S) * N S ^ 2

lemma dw_nonneg {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {S : ℕ} (hS : S < 2 ^ n) :
    0 ≤ dw n N S := delta_term_nonneg hsol hS

lemma exists_testBit {S : ℕ} (h : S ≠ 0) : ∃ j, S.testBit j = true := by
  by_contra hc
  push_neg at hc
  refine h (Nat.eq_of_testBit_eq fun j => ?_)
  rw [Nat.zero_testBit]
  simpa using hc j

/-- every nonempty set in the support of an all-mass-4 solution has coefficient ±1 -/
lemma coeff_sq_one {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N)
    (hm : ∀ v, v < n → mass n N v = 4) {S : ℕ} (hS : S < 2 ^ n) (hne : S ≠ 0) (hN : N S ≠ 0) :
    N S ^ 2 = 1 := by
  obtain ⟨j, hj⟩ := exists_testBit hne
  have hjn : j < n := lt_of_testBit hS hj
  have hmem : S ∈ supp n N j := mem_supp.mpr ⟨hS, hj, hN⟩
  rcases mass_four_pm hsol hjn (hm j hjn) S hmem with h | h <;> rw [h] <;> ring

/-- `δ = 4` when every mass is 4 and `n = 11` -/
lemma delta_eq_four {N : ℕ → ℤ} (hsol : IsSol 11 N) (hm : ∀ v, v < 11 → mass 11 N v = 4) :
    ∑ S ∈ range (2 ^ 11), dw 11 N S = 4 := by
  have hb := bookkeeping hsol
  have hz : ∑ v ∈ range 11, (mass 11 N v - 4) = 0 :=
    Finset.sum_eq_zero fun v hv => by rw [hm v (mem_range.mp hv)]; ring
  rw [hz, zero_add] at hb
  simp only [dw]
  rw [hb]; norm_num

/-- any sub-family of the support has `δ`-weight at most 4 -/
lemma sum_dw_le {N : ℕ → ℤ} (hsol : IsSol 11 N) (hm : ∀ v, v < 11 → mass 11 N v = 4)
    {A : Finset ℕ} (hA : A ⊆ range (2 ^ 11)) : ∑ S ∈ A, dw 11 N S ≤ 4 := by
  rw [← delta_eq_four hsol hm]
  exact Finset.sum_le_sum_of_subset_of_nonneg hA
    (fun S hS _ => dw_nonneg hsol (mem_range.mp hS))

/-- a sub-family of total weight 4 carries all of `δ`: every other set is cubic -/
lemma dw_saturate {N : ℕ → ℤ} (hsol : IsSol 11 N) (hm : ∀ v, v < 11 → mass 11 N v = 4)
    {A : Finset ℕ} (hA : A ⊆ range (2 ^ 11)) (hsum : ∑ S ∈ A, dw 11 N S = 4)
    {S : ℕ} (hS : S < 2 ^ 11) (hSA : S ∉ A) : dw 11 N S = 0 := by
  have hins : insert S A ⊆ range (2 ^ 11) := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx'
    · exact mem_range.mpr hS
    · exact hA hx'
  have h := sum_dw_le hsol hm hins
  rw [Finset.sum_insert hSA, hsum] at h
  have h0 := dw_nonneg hsol hS
  omega

/-- while the budget is not spent there is a further set of positive `δ`-weight -/
lemma exists_dw_outside {N : ℕ → ℤ} (hsol : IsSol 11 N) (hm : ∀ v, v < 11 → mass 11 N v = 4)
    {A : Finset ℕ} (hA : A ⊆ range (2 ^ 11)) (hsum : ∑ S ∈ A, dw 11 N S < 4) :
    ∃ S, S < 2 ^ 11 ∧ S ∉ A ∧ dw 11 N S ≠ 0 := by
  by_contra hc
  push_neg at hc
  have hzero : ∀ S ∈ range (2 ^ 11), S ∉ A → dw 11 N S = 0 :=
    fun S hS hSA => hc S (mem_range.mp hS) hSA
  have := Finset.sum_subset hA hzero
  rw [delta_eq_four hsol hm] at this
  omega

/-! ### The weight of a low-degree set -/

lemma dw_quad {N : ℕ → ℤ} (hsol : IsSol 11 N) (hm : ∀ v, v < 11 → mass 11 N v = 4)
    {S : ℕ} (hS : S < 2 ^ 11) (hN : N S ≠ 0) (hc : card 11 S = 2) : dw 11 N S = 1 := by
  have hne : S ≠ 0 := by
    rintro rfl
    rw [card_zero_eq_zero] at hc; omega
  simp only [dw, hc, coeff_sq_one hsol hm hS hne hN]; norm_num

lemma dw_lin {N : ℕ → ℤ} (hsol : IsSol 11 N) (hm : ∀ v, v < 11 → mass 11 N v = 4)
    {S : ℕ} (hS : S < 2 ^ 11) (hN : N S ≠ 0) (hc : card 11 S = 1) : dw 11 N S = 2 := by
  have hne : S ≠ 0 := by
    rintro rfl
    rw [card_zero_eq_zero] at hc; omega
  simp only [dw, hc, coeff_sq_one hsol hm hS hne hN]; norm_num

/-- the constant term, if present, has coefficient ±1 and weight 3 -/
lemma dw_const {N : ℕ → ℤ} (hsol : IsSol 11 N) (hm : ∀ v, v < 11 → mass 11 N v = 4)
    (hN : N 0 ≠ 0) : dw 11 N 0 = 3 := by
  have hzlt : (0 : ℕ) < 2 ^ 11 := Nat.two_pow_pos 11
  have hsub : ({0} : Finset ℕ) ⊆ range (2 ^ 11) := by
    intro x hx; rw [mem_singleton] at hx; subst hx; exact mem_range.mpr hzlt
  have h := sum_dw_le hsol hm hsub
  rw [Finset.sum_singleton] at h
  have hsq : 1 ≤ N 0 ^ 2 := one_le_sq_of_ne_zero hN
  simp only [dw, card_zero_eq_zero] at h ⊢
  push_cast at h ⊢
  obtain ⟨x, hxdef⟩ : ∃ x, N 0 ^ 2 = x := ⟨_, rfl⟩
  rw [hxdef] at h hsq ⊢
  omega

/-- a set of nonzero coefficient and positive weight has size 0, 1 or 2 -/
lemma card_le_two_of_dw_ne {N : ℕ → ℤ} (hsol : IsSol 11 N) {S : ℕ} (hS : S < 2 ^ 11)
    (hw : dw 11 N S ≠ 0) : N S ≠ 0 ∧ card 11 S ≤ 2 := by
  simp only [dw] at hw
  constructor
  · intro h; rw [h] at hw; simp at hw
  · by_contra hc
    push_neg at hc
    have hcz : card 11 S = 3 ∨ 3 < card 11 S := by omega
    rcases hcz with h | h
    · rw [h] at hw; norm_num at hw
    · rw [hsol.1 S hS h] at hw; simp at hw

lemma card_three_of_dw_zero {N : ℕ → ℤ} {S : ℕ} (hN : N S ≠ 0) (hw : dw 11 N S = 0) :
    card 11 S = 3 := by
  simp only [dw] at hw
  rcases mul_eq_zero.mp hw with h | h
  · have : ((card 11 S : ℕ) : ℤ) = 3 := by linarith
    exact_mod_cast this
  · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hN

/-- a set of positive `δ`-weight is a linear term (weight 2) or a quadratic term (weight 1) -/
lemma low_set_shape {N : ℕ → ℤ} (hsol : IsSol 11 N) (hm : ∀ v, v < 11 → mass 11 N v = 4)
    (hconst : N 0 = 0) {S : ℕ} (hS : S < 2 ^ 11) (hw : dw 11 N S ≠ 0) :
    (∃ i, i < 11 ∧ S = 2 ^ i ∧ dw 11 N S = 2) ∨
    (∃ a b, a < 11 ∧ b < 11 ∧ a ≠ b ∧ S = pair a b ∧ dw 11 N S = 1) := by
  obtain ⟨hN, hc2⟩ := card_le_two_of_dw_ne hsol hS hw
  interval_cases h : card 11 S
  · exact absurd (by rw [eq_zero_of_card_zero hS h] at hN; exact hN) (by simpa [hconst])
  · obtain ⟨i, hi, rfl⟩ := exists_two_pow_of_card_one hS h
    exact Or.inl ⟨i, hi, rfl, dw_lin hsol hm hS hN h⟩
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := exists_pair_of_card_two hS h
    exact Or.inr ⟨a, b, ha, hb, hab, rfl, dw_quad hsol hm hS hN h⟩

/-- **No constant term.**  A constant term costs 3 of the budget 4, and the remaining 1 must
be spent, but every further low-degree term drags a partner along (`quad_deg_two`) or costs 2. -/
theorem delta_four_no_const {N : ℕ → ℤ} (hsol : IsSol 11 N)
    (hm : ∀ v, v < 11 → mass 11 N v = 4) : N 0 = 0 := by
  by_contra hN0
  have hzlt : (0 : ℕ) < 2 ^ 11 := Nat.two_pow_pos 11
  have hsub : ({0} : Finset ℕ) ⊆ range (2 ^ 11) := by
    intro x hx; rw [mem_singleton] at hx; subst hx; exact mem_range.mpr hzlt
  have hs1 : ∑ S ∈ ({0} : Finset ℕ), dw 11 N S = 3 := by
    rw [Finset.sum_singleton]; exact dw_const hsol hm hN0
  obtain ⟨S, hS, hSA, hw⟩ := exists_dw_outside hsol hm hsub (by rw [hs1]; norm_num)
  have hSne : S ≠ 0 := by intro h; exact hSA (by simp [h])
  obtain ⟨hNS, hc2⟩ := card_le_two_of_dw_ne hsol hS hw
  have hc0 : card 11 S ≠ 0 := fun h => hSne (eq_zero_of_card_zero hS h)
  -- a linear term would cost 2 more, overshooting the budget
  have hnotlin : card 11 S ≠ 1 := by
    intro h
    have h2 := dw_lin hsol hm hS hNS h
    have hsub2 : ({0, S} : Finset ℕ) ⊆ range (2 ^ 11) := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_range.mpr hzlt
      · exact mem_range.mpr hS
    have := sum_dw_le hsol hm hsub2
    rw [Finset.sum_insert (by simp [Ne.symm hSne]), Finset.sum_singleton,
      dw_const hsol hm hN0, h2] at this
    omega
  -- so it is a quadratic, and `quad_deg_two` supplies a second one: 3 + 1 + 1 > 4
  have hc : card 11 S = 2 := by omega
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := exists_pair_of_card_two hS hc
  obtain ⟨y, hy, hya, hyb, hNy⟩ :=
    quad_deg_two hsol ha hb (Ne.symm hab) (hm a ha) hNS
  have hQ2lt : pair a y < 2 ^ 11 := by
    unfold pair
    exact Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) ha)
      (Nat.pow_lt_pow_right (by norm_num) hy)
  have hQ2c : card 11 (pair a y) = 2 := card_pair_eq ha hy (Ne.symm hya)
  have hne12 : pair a b ≠ pair a y := by
    intro h
    rcases pair_eq_iff.mp h with ⟨-, hb'⟩ | ⟨ha', -⟩
    · exact hyb hb'.symm
    · exact hya ha'.symm
  have hsub3 : ({0, pair a b, pair a y} : Finset ℕ) ⊆ range (2 ^ 11) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem_range.mpr hzlt
    · exact mem_range.mpr hS
    · exact mem_range.mpr hQ2lt
  have hfin := sum_dw_le hsol hm hsub3
  rw [Finset.sum_insert (by simp [Ne.symm hSne, Ne.symm (show pair a y ≠ 0 from pair_ne_zero)]),
    Finset.sum_insert (by simp [hne12]), Finset.sum_singleton,
    dw_const hsol hm hN0, dw_quad hsol hm hS hNS hc,
    dw_quad hsol hm hQ2lt hNy hQ2c] at hfin
  omega

lemma pair_lt_two_pow {n u w : ℕ} (hu : u < n) (hw : w < n) : pair u w < 2 ^ n := by
  unfold pair
  exact Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) hu)
    (Nat.pow_lt_pow_right (by norm_num) hw)

/-- **The `δ = 4` case has exactly two shapes.**  Of the five partitions `{4}, {3,1}, {2,2},
`{2,1,1}`, `{1,1,1,1}` of the lower-order weight listed in R3_equals_10.md, three are
impossible: `{4}` because a ±2 coefficient cannot sit on a set all of whose vertices have
mass 4, and `{3,1}`, `{2,1,1}` because a quadratic term never comes alone (`quad_deg_two`).
What survives is `{2,2}` — two linear terms, no quadratics — and `{1,1,1,1}` — four
quadratics, nothing else below the top level. -/
theorem delta_four_structure {N : ℕ → ℤ} (hsol : IsSol 11 N)
    (hm : ∀ v, v < 11 → mass 11 N v = 4) :
    (∃ i j, i < 11 ∧ j < 11 ∧ i ≠ j ∧ N (2 ^ i) ≠ 0 ∧ N (2 ^ j) ≠ 0 ∧
        ∀ S, S < 2 ^ 11 → N S ≠ 0 → S = 2 ^ i ∨ S = 2 ^ j ∨ card 11 S = 3) ∨
    (∃ Q1 Q2 Q3 Q4 : ℕ, Q1 ≠ Q2 ∧ Q1 ≠ Q3 ∧ Q1 ≠ Q4 ∧ Q2 ≠ Q3 ∧ Q2 ≠ Q4 ∧ Q3 ≠ Q4 ∧
        (∀ Q ∈ ({Q1, Q2, Q3, Q4} : Finset ℕ), Q < 2 ^ 11 ∧ N Q ≠ 0 ∧ card 11 Q = 2) ∧
        ∀ S, S < 2 ^ 11 → N S ≠ 0 →
          S = Q1 ∨ S = Q2 ∨ S = Q3 ∨ S = Q4 ∨ card 11 S = 3) := by
  have hconst := delta_four_no_const hsol hm
  by_cases hq : ∃ a b, a < 11 ∧ b < 11 ∧ a ≠ b ∧ N (pair a b) ≠ 0
  · -- a quadratic exists: `quad_deg_two` at both its endpoints gives three, and the last
    -- unit of budget must be a fourth quadratic
    right
    obtain ⟨a, b, ha, hb, hab, hNab⟩ := hq
    obtain ⟨y, hy, hya, hyb, hNay⟩ := quad_deg_two hsol ha hb (Ne.symm hab) (hm a ha) hNab
    have hNba : N (pair b a) ≠ 0 := by rwa [pair_comm]
    obtain ⟨z, hz, hzb, hza, hNbz⟩ := quad_deg_two hsol hb ha hab (hm b hb) hNba
    have L1 : pair a b < 2 ^ 11 := pair_lt_two_pow ha hb
    have L2 : pair a y < 2 ^ 11 := pair_lt_two_pow ha hy
    have L3 : pair b z < 2 ^ 11 := pair_lt_two_pow hb hz
    have C1 : card 11 (pair a b) = 2 := card_pair_eq ha hb hab
    have C2 : card 11 (pair a y) = 2 := card_pair_eq ha hy (Ne.symm hya)
    have C3 : card 11 (pair b z) = 2 := card_pair_eq hb hz (Ne.symm hzb)
    have n12 : pair a b ≠ pair a y := by
      intro h
      rcases pair_eq_iff.mp h with ⟨-, h'⟩ | ⟨-, h'⟩
      · exact hyb h'.symm
      · exact hab h'.symm
    have n13 : pair a b ≠ pair b z := by
      intro h
      rcases pair_eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
      · exact hab h'
      · exact hza h'.symm
    have n23 : pair a y ≠ pair b z := by
      intro h
      rcases pair_eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
      · exact hab h'
      · exact hza h'.symm
    have hsub3 : ({pair a b, pair a y, pair b z} : Finset ℕ) ⊆ range (2 ^ 11) := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      exacts [mem_range.mpr L1, mem_range.mpr L2, mem_range.mpr L3]
    have hs3 : ∑ S ∈ ({pair a b, pair a y, pair b z} : Finset ℕ), dw 11 N S = 3 := by
      rw [Finset.sum_insert (by simp [n12, n13]), Finset.sum_insert (by simp [n23]),
        Finset.sum_singleton, dw_quad hsol hm L1 hNab C1, dw_quad hsol hm L2 hNay C2,
        dw_quad hsol hm L3 hNbz C3]
      norm_num
    obtain ⟨Q4, hQ4lt, hQ4A, hQ4w⟩ := exists_dw_outside hsol hm hsub3 (by rw [hs3]; norm_num)
    simp only [mem_insert, mem_singleton, not_or] at hQ4A
    obtain ⟨n14, n24, n34⟩ := hQ4A
    have hsub4 : (insert Q4 ({pair a b, pair a y, pair b z} : Finset ℕ)) ⊆ range (2 ^ 11) := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx'
      · exact mem_range.mpr hQ4lt
      · exact hsub3 hx'
    have hnotmem : Q4 ∉ ({pair a b, pair a y, pair b z} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton, not_or]; exact ⟨n14, n24, n34⟩
    have hbound := sum_dw_le hsol hm hsub4
    rw [Finset.sum_insert hnotmem, hs3] at hbound
    -- the fourth term is a quadratic: a linear term would cost 2 and overshoot
    rcases low_set_shape hsol hm hconst hQ4lt hQ4w with ⟨i, hi, rfl, hwi⟩ | ⟨c, d, hc, hd, hcd, rfl, hwq⟩
    · rw [hwi] at hbound; omega
    · have hsum4 : ∑ S ∈ (insert (pair c d) ({pair a b, pair a y, pair b z} : Finset ℕ)),
          dw 11 N S = 4 := by
        rw [Finset.sum_insert hnotmem, hs3, hwq]; norm_num
      have hNQ4 : N (pair c d) ≠ 0 := (card_le_two_of_dw_ne hsol hQ4lt hQ4w).1
      have hCQ4 : card 11 (pair c d) = 2 := card_pair_eq hc hd hcd
      refine ⟨pair a b, pair a y, pair b z, pair c d, n12, n13, Ne.symm n14, n23,
        Ne.symm n24, Ne.symm n34, ?_, ?_⟩
      · intro Q hQ
        simp only [mem_insert, mem_singleton] at hQ
        rcases hQ with rfl | rfl | rfl | rfl
        exacts [⟨L1, hNab, C1⟩, ⟨L2, hNay, C2⟩, ⟨L3, hNbz, C3⟩, ⟨hQ4lt, hNQ4, hCQ4⟩]
      · intro S hS hNS
        by_cases hmem : S ∈ (insert (pair c d) ({pair a b, pair a y, pair b z} : Finset ℕ))
        · simp only [mem_insert, mem_singleton] at hmem
          rcases hmem with rfl | rfl | rfl | rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            (card_three_of_dw_zero hNS (dw_saturate hsol hm hsub4 hsum4 hS hmem)))))
  · -- no quadratic at all: the budget 4 is two linear terms
    left
    push_neg at hq
    have hnoquad : ∀ S, S < 2 ^ 11 → N S ≠ 0 → card 11 S ≠ 2 := by
      intro S hS hNS hc
      obtain ⟨u, w, hu, hw, huw, rfl⟩ := exists_pair_of_card_two hS hc
      exact hNS (hq u w hu hw huw)
    have hemp : (∅ : Finset ℕ) ⊆ range (2 ^ 11) := Finset.empty_subset _
    obtain ⟨S1, hS1lt, -, hS1w⟩ := exists_dw_outside hsol hm hemp (by simp)
    rcases low_set_shape hsol hm hconst hS1lt hS1w with ⟨i, hi, rfl, hwi⟩ | ⟨u, w, hu, hw, huw, rfl, -⟩
    swap
    · exact absurd (card_pair_eq hu hw huw)
        (hnoquad _ hS1lt (card_le_two_of_dw_ne hsol hS1lt hS1w).1)
    have hNi : N (2 ^ i) ≠ 0 := (card_le_two_of_dw_ne hsol hS1lt hS1w).1
    have hsub1 : ({2 ^ i} : Finset ℕ) ⊆ range (2 ^ 11) := by
      intro x hx; rw [mem_singleton] at hx; subst hx; exact mem_range.mpr hS1lt
    have hs1 : ∑ S ∈ ({2 ^ i} : Finset ℕ), dw 11 N S = 2 := by
      rw [Finset.sum_singleton]; exact hwi
    obtain ⟨S2, hS2lt, hS2A, hS2w⟩ := exists_dw_outside hsol hm hsub1 (by rw [hs1]; norm_num)
    rw [mem_singleton] at hS2A
    rcases low_set_shape hsol hm hconst hS2lt hS2w with ⟨j, hj, rfl, hwj⟩ | ⟨u, w, hu, hw, huw, rfl, -⟩
    swap
    · exact absurd (card_pair_eq hu hw huw)
        (hnoquad _ hS2lt (card_le_two_of_dw_ne hsol hS2lt hS2w).1)
    have hNj : N (2 ^ j) ≠ 0 := (card_le_two_of_dw_ne hsol hS2lt hS2w).1
    have hij : i ≠ j := by rintro rfl; exact hS2A rfl
    have hsub2 : ({2 ^ i, 2 ^ j} : Finset ℕ) ⊆ range (2 ^ 11) := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      exacts [mem_range.mpr hS1lt, mem_range.mpr hS2lt]
    have hsum2 : ∑ S ∈ ({2 ^ i, 2 ^ j} : Finset ℕ), dw 11 N S = 4 := by
      rw [Finset.sum_insert (by simp [Ne.symm hS2A]), Finset.sum_singleton, hwi, hwj]
      norm_num
    refine ⟨i, j, hi, hj, hij, hNi, hNj, ?_⟩
    intro S hS hNS
    by_cases hmem : S ∈ ({2 ^ i, 2 ^ j} : Finset ℕ)
    · simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with rfl | rfl
      exacts [Or.inl rfl, Or.inr (Or.inl rfl)]
    · exact Or.inr (Or.inr (card_three_of_dw_zero hNS (dw_saturate hsol hm hsub2 hsum2 hS hmem)))

/-- **Exactly two quadratics.**  At a mass-4 vertex carrying the quadratic term `{v, x}`
there is exactly one further quadratic `{v, y}`, and no others.  (A link containing a
singleton is L2 or L3, and each of those contains exactly two singletons.) -/
theorem quad_exactly_two {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v x : ℕ} (hv : v < n)
    (hx : x < n) (hxv : x ≠ v) (h4 : mass n N v = 4) (hq : N (pair v x) ≠ 0) :
    ∃ y, y < n ∧ y ≠ v ∧ y ≠ x ∧ N (pair v y) ≠ 0 ∧
      ∀ w, w < n → w ≠ v → N (pair v w) ≠ 0 → w = x ∨ w = y := by
  have hmem : (2 : ℕ) ^ x ∈ link n N v := (two_pow_mem_link hv hx hxv).mpr hq
  rcases mass_four_link_cover hsol hv h4 with
    ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, hL⟩ | ⟨a, b, hab, hL⟩ |
    ⟨a, b, c, hab, hac, hbc, hL⟩ | ⟨a, b, c, hab, hac, hbc, hL⟩
  · exfalso
    rw [hL] at hmem
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact pair_ne_two_pow hpq h.symm
    · exact pair_ne_two_pow hqr h.symm
    · exact pair_ne_two_pow hrs h.symm
    · exact pair_ne_two_pow (Ne.symm hps) h.symm
  · have honly : ∀ w, w < n → w ≠ v → N (pair v w) ≠ 0 → w = a ∨ w = b := by
      intro w hw hwv hNw
      have hm := (two_pow_mem_link hv hw hwv).mpr hNw
      rw [hL] at hm
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with h | h | h | h
      · exact absurd h (Nat.two_pow_pos w).ne'
      · exact Or.inl (Nat.pow_right_injective (le_refl 2) h)
      · exact Or.inr (Nat.pow_right_injective (le_refl 2) h)
      · exact absurd h.symm (pair_ne_two_pow hab)
    have hA : (2 : ℕ) ^ a ∈ link n N v := by rw [hL]; simp
    have hB : (2 : ℕ) ^ b ∈ link n N v := by rw [hL]; simp
    obtain ⟨han, hav, haq⟩ := link_two_pow hv hA
    obtain ⟨hbn, hbv, hbq⟩ := link_two_pow hv hB
    rcases honly x hx hxv hq with rfl | rfl
    · exact ⟨b, hbn, hbv, Ne.symm hab, hbq, fun w hw hwv hNw =>
        (honly w hw hwv hNw)⟩
    · exact ⟨a, han, hav, hab, haq, fun w hw hwv hNw =>
        (honly w hw hwv hNw).symm⟩
  · have honly : ∀ w, w < n → w ≠ v → N (pair v w) ≠ 0 → w = a ∨ w = b := by
      intro w hw hwv hNw
      have hm := (two_pow_mem_link hv hw hwv).mpr hNw
      rw [hL] at hm
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with h | h | h | h
      · exact Or.inl (Nat.pow_right_injective (le_refl 2) h)
      · exact Or.inr (Nat.pow_right_injective (le_refl 2) h)
      · exact absurd h.symm (pair_ne_two_pow hac)
      · exact absurd h.symm (pair_ne_two_pow hbc)
    have hA : (2 : ℕ) ^ a ∈ link n N v := by rw [hL]; simp
    have hB : (2 : ℕ) ^ b ∈ link n N v := by rw [hL]; simp
    obtain ⟨han, hav, haq⟩ := link_two_pow hv hA
    obtain ⟨hbn, hbv, hbq⟩ := link_two_pow hv hB
    rcases honly x hx hxv hq with rfl | rfl
    · exact ⟨b, hbn, hbv, Ne.symm hab, hbq, fun w hw hwv hNw =>
        (honly w hw hwv hNw)⟩
    · exact ⟨a, han, hav, hab, haq, fun w hw hwv hNw =>
        (honly w hw hwv hNw).symm⟩
  · exfalso
    rw [hL] at hmem
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact absurd h (Nat.two_pow_pos x).ne'
    · exact pair_ne_two_pow hab h.symm
    · exact pair_ne_two_pow hbc h.symm
    · exact pair_ne_two_pow hac h.symm

/-! ## The `{1,1,1,1}` sub-case: an L3 vertex and its apex -/

/-- **L3 in full.**  A mass-4 vertex with no linear term but with a quadratic term has an L3
link: two quadratics `{v,p}, {v,q}` and two cubics `{v,p,r}, {v,q,r}` through a single
*apex* `r`, and nothing else. -/
theorem link_L3 {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n)
    (h4 : mass n N v = 4) (hnolin : N (2 ^ v) = 0)
    {x : ℕ} (hx : x < n) (hxv : x ≠ v) (hqx : N (pair v x) ≠ 0) :
    ∃ p q r, p < n ∧ q < n ∧ r < n ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      p ≠ v ∧ q ≠ v ∧ r ≠ v ∧ (x = p ∨ x = q) ∧
      N (pair v p) ≠ 0 ∧ N (pair v q) ≠ 0 ∧ N (tri v p r) ≠ 0 ∧ N (tri v q r) ≠ 0 ∧
      ∀ S, S < 2 ^ n → N S ≠ 0 → S.testBit v = true →
        S = pair v p ∨ S = pair v q ∨ S = tri v p r ∨ S = tri v q r := by
  have hmem : (2 : ℕ) ^ x ∈ link n N v := (two_pow_mem_link hv hx hxv).mpr hqx
  rcases mass_four_link_cover hsol hv h4 with
    ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, hL⟩ | ⟨a, b, hab, hL⟩ |
    ⟨a, b, c, hab, hac, hbc, hL⟩ | ⟨a, b, c, hab, hac, hbc, hL⟩
  · exfalso
    rw [hL] at hmem
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact pair_ne_two_pow hpq h.symm
    · exact pair_ne_two_pow hqr h.symm
    · exact pair_ne_two_pow hrs h.symm
    · exact pair_ne_two_pow (Ne.symm hps) h.symm
  · exact absurd ((zero_mem_link hv).mp (by rw [hL]; simp)) (by simpa using hnolin)
  · refine ⟨a, b, c, ?_⟩
    have hA : (2 : ℕ) ^ a ∈ link n N v := by rw [hL]; simp
    have hB : (2 : ℕ) ^ b ∈ link n N v := by rw [hL]; simp
    have hAC : pair a c ∈ link n N v := by rw [hL]; simp
    have hBC : pair b c ∈ link n N v := by rw [hL]; simp
    obtain ⟨han, hav, haq⟩ := link_two_pow hv hA
    obtain ⟨hbn, hbv, hbq⟩ := link_two_pow hv hB
    obtain ⟨-, hcn, -, hcv, hac3⟩ := link_pair hv hAC
    obtain ⟨-, -, -, -, hbc3⟩ := link_pair hv hBC
    have hxab : x = a ∨ x = b := by
      rw [hL] at hmem
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with h | h | h | h
      · exact Or.inl (Nat.pow_right_injective (le_refl 2) h)
      · exact Or.inr (Nat.pow_right_injective (le_refl 2) h)
      · exact absurd h.symm (pair_ne_two_pow hac)
      · exact absurd h.symm (pair_ne_two_pow hbc)
    refine ⟨han, hbn, hcn, hab, hac, hbc, hav, hbv, hcv, hxab, haq, hbq, hac3, hbc3, ?_⟩
    intro S hS hNS hSb
    have hT : S ^^^ 2 ^ v ∈ link n N v :=
      mem_link.mpr (by rw [xor_two_pow_invol]; exact mem_supp.mpr ⟨hS, hSb, hNS⟩)
    rw [hL] at hT
    simp only [mem_insert, mem_singleton] at hT
    have hback : ∀ T : ℕ, S ^^^ 2 ^ v = T → S = T ^^^ 2 ^ v := by
      intro T hT'; rw [← hT', xor_two_pow_invol]
    rcases hT with h | h | h | h
    · exact Or.inl (by rw [hback _ h, two_pow_xor_two_pow hav, pair_comm])
    · exact Or.inr (Or.inl (by rw [hback _ h, two_pow_xor_two_pow hbv, pair_comm]))
    · exact Or.inr (Or.inr (Or.inl (by rw [hback _ h, pair_xor_two_pow hav hcv])))
    · exact Or.inr (Or.inr (Or.inr (by rw [hback _ h, pair_xor_two_pow hbv hcv])))
  · exact absurd ((zero_mem_link hv).mp (by rw [hL]; simp)) (by simpa using hnolin)

/-- `link_L3` normalised so that the given quadratic neighbour `x` occupies the first slot:
the support at `v` is `{v,x}, {v,w}, {v,x,r}, {v,w,r}` and nothing else. -/
theorem link_L3' {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n)
    (h4 : mass n N v = 4) (hnolin : N (2 ^ v) = 0)
    {x : ℕ} (hx : x < n) (hxv : x ≠ v) (hqx : N (pair v x) ≠ 0) :
    ∃ w r, w < n ∧ r < n ∧ w ≠ x ∧ w ≠ r ∧ x ≠ r ∧ w ≠ v ∧ r ≠ v ∧
      N (pair v w) ≠ 0 ∧ N (tri v x r) ≠ 0 ∧ N (tri v w r) ≠ 0 ∧
      ∀ S, S < 2 ^ n → N S ≠ 0 → S.testBit v = true →
        S = pair v x ∨ S = pair v w ∨ S = tri v x r ∨ S = tri v w r := by
  obtain ⟨p, q, r, hpn, hqn, hrn, hpq, hpr, hqr, hpv, hqv, hrv, hxpq,
    hNp, hNq, hNpr, hNqr, hsupp⟩ := link_L3 hsol hv h4 hnolin hx hxv hqx
  rcases hxpq with rfl | rfl
  · exact ⟨q, r, hqn, hrn, Ne.symm hpq, hqr, hpr, hqv, hrv, hNq, hNpr, hNqr, hsupp⟩
  · refine ⟨p, r, hpn, hrn, hpq, hpr, hqr, hpv, hrv, hNp, hNqr, hNpr, ?_⟩
    intro S hS hNS hSb
    rcases hsupp S hS hNS hSb with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))

/-- **The apexes of two quadratic-adjacent L3 vertices agree.**  `a`'s cubic `{a,b,rₐ}` must
be one of `b`'s two cubics `{b,a,r_b}`, `{b,q_b,r_b}`; the second would force `a = r_b`. -/
lemma apex_eq {n : ℕ} {N : ℕ → ℤ} {a b qb ra rb : ℕ}
    (han : a < n) (hbn : b < n) (hran : ra < n)
    (hraa : ra ≠ a) (hrab : ra ≠ b) (hab : a ≠ b) (hqba : qb ≠ a) (hrba : rb ≠ a)
    (hcub : N (tri a b ra) ≠ 0)
    (Hb : ∀ S, S < 2 ^ n → N S ≠ 0 → S.testBit b = true →
      S = pair b a ∨ S = pair b qb ∨ S = tri b a rb ∨ S = tri b qb rb) :
    ra = rb := by
  have hlt : tri a b ra < 2 ^ n := tri_lt han hbn hran
  have hbit : (tri a b ra).testBit b = true := mem_tri_iff.mpr (Or.inr (Or.inl rfl))
  rcases Hb _ hlt hcub hbit with h | h | h | h
  · exfalso
    have hb : (pair b a).testBit ra = true := by
      rw [← h]; exact mem_tri_iff.mpr (Or.inr (Or.inr rfl))
    rcases mem_pair_iff.mp hb with h' | h'
    · exact hrab h'
    · exact hraa h'
  · exfalso
    have hb : (pair b qb).testBit a = true := by rw [← h]; exact mem_tri_iff.mpr (Or.inl rfl)
    rcases mem_pair_iff.mp hb with h' | h'
    · exact hab h'
    · exact hqba h'.symm
  · have hb : (tri b a rb).testBit ra = true := by
      rw [← h]; exact mem_tri_iff.mpr (Or.inr (Or.inr rfl))
    rcases mem_tri_iff.mp hb with h' | h' | h'
    · exact absurd h' hrab
    · exact absurd h' hraa
    · exact h'
  · exfalso
    have hb : (tri b qb rb).testBit a = true := by rw [← h]; exact mem_tri_iff.mpr (Or.inl rfl)
    rcases mem_tri_iff.mp hb with h' | h' | h'
    · exact hab h'
    · exact hqba h'.symm
    · exact hrba h'.symm

/-! ### Counting helpers for the four quadratics -/

lemma card_tri_eq {n a b c : ℕ} (ha : a < n) (hb : b < n) (hc : c < n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : card n (tri a b c) = 3 := by
  unfold card
  have hfil : (range n).filter (fun i => (tri a b c).testBit i) = {a, b, c} := by
    ext j
    simp only [mem_filter, mem_range, mem_insert, mem_singleton]
    constructor
    · rintro ⟨-, hj⟩; exact mem_tri_iff.mp hj
    · rintro (rfl | rfl | rfl)
      exacts [⟨ha, mem_tri_iff.mpr (Or.inl rfl)⟩, ⟨hb, mem_tri_iff.mpr (Or.inr (Or.inl rfl))⟩,
        ⟨hc, mem_tri_iff.mpr (Or.inr (Or.inr rfl))⟩]
  rw [hfil, card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]

lemma five_in_four {P1 P2 P3 P4 P5 Q1 Q2 Q3 Q4 : ℕ}
    (e12 : P1 ≠ P2) (e13 : P1 ≠ P3) (e14 : P1 ≠ P4) (e15 : P1 ≠ P5)
    (e23 : P2 ≠ P3) (e24 : P2 ≠ P4) (e25 : P2 ≠ P5)
    (e34 : P3 ≠ P4) (e35 : P3 ≠ P5) (e45 : P4 ≠ P5)
    (hsub : ({P1, P2, P3, P4, P5} : Finset ℕ) ⊆ {Q1, Q2, Q3, Q4}) : False := by
  have h5 : ({P1, P2, P3, P4, P5} : Finset ℕ).card = 5 := by
    rw [card_insert_of_notMem (by simp [e12, e13, e14, e15]),
      card_insert_of_notMem (by simp [e23, e24, e25]),
      card_insert_of_notMem (by simp [e34, e35]), card_pair e45]
  have hle := Finset.card_le_card hsub
  rw [h5] at hle
  have := card_quad_le Q1 Q2 Q3 Q4
  omega

lemma exists_fourth {P1 P2 P3 Q1 Q2 Q3 Q4 : ℕ}
    (e12 : P1 ≠ P2) (e13 : P1 ≠ P3) (e23 : P2 ≠ P3)
    (hsub : ({P1, P2, P3} : Finset ℕ) ⊆ {Q1, Q2, Q3, Q4})
    (hQcard : ({Q1, Q2, Q3, Q4} : Finset ℕ).card = 4) :
    ∃ P, P ∈ ({Q1, Q2, Q3, Q4} : Finset ℕ) ∧ P ≠ P1 ∧ P ≠ P2 ∧ P ≠ P3 := by
  have h3 : ({P1, P2, P3} : Finset ℕ).card = 3 := by
    rw [card_insert_of_notMem (by simp [e12, e13]), card_pair e23]
  have hss : ({P1, P2, P3} : Finset ℕ) ⊂ {Q1, Q2, Q3, Q4} := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
    intro h
    rw [h, hQcard] at h3
    omega
  obtain ⟨P, hPQ, hPn⟩ := Finset.exists_of_ssubset hss
  simp only [mem_insert, mem_singleton, not_or] at hPn
  exact ⟨P, hPQ, hPn.1, hPn.2.1, hPn.2.2⟩

/-! ### The `{1,1,1,1}` closure -/

/-- **The 4-cycle with its apex is closed, and that is a contradiction.**  Given the quadratic
4-cycle `a-b-wb-wa-a` and the common apex `c`, the five vertices carry the whole of their
support, so `no_crossing_split` applies. -/
lemma eleven_cycle_closed {N : ℕ → ℤ} (hsol : IsSol 11 N)
    (hm : ∀ v, v < 11 → mass 11 N v = 4)
    {a b wa wb c : ℕ}
    (ha : a < 11) (hb : b < 11) (hwan : wa < 11) (hwbn : wb < 11) (hcn : c < 11)
    (hab : a ≠ b) (hawa : a ≠ wa) (hawb : a ≠ wb) (hac : a ≠ c)
    (hbwa : b ≠ wa) (hbwb : b ≠ wb) (hbc : b ≠ c)
    (hwawb : wa ≠ wb) (hwac : wa ≠ c) (hwbc : wb ≠ c)
    (hNab : N (pair a b) ≠ 0)
    (hNabc : N (tri a b c) ≠ 0) (hNawac : N (tri a wa c) ≠ 0) (hNbwbc : N (tri b wb c) ≠ 0)
    (hNwawbc : N (tri wa wb c) ≠ 0)
    (Ha : ∀ S, S < 2 ^ 11 → N S ≠ 0 → S.testBit a = true →
      S = pair a b ∨ S = pair a wa ∨ S = tri a b c ∨ S = tri a wa c)
    (Hb : ∀ S, S < 2 ^ 11 → N S ≠ 0 → S.testBit b = true →
      S = pair b a ∨ S = pair b wb ∨ S = tri b a c ∨ S = tri b wb c)
    (Hwa : ∀ S, S < 2 ^ 11 → N S ≠ 0 → S.testBit wa = true →
      S = pair wa a ∨ S = pair wa wb ∨ S = tri wa a c ∨ S = tri wa wb c)
    (Hwb : ∀ S, S < 2 ^ 11 → N S ≠ 0 → S.testBit wb = true →
      S = pair wb b ∨ S = pair wb wa ∨ S = tri wb b c ∨ S = tri wb wa c) :
    False := by
  have htrifalse : ∀ x y z j : ℕ, j ≠ x → j ≠ y → j ≠ z → (tri x y z).testBit j = false := by
    intro x y z j h1 h2 h3
    cases hbit : (tri x y z).testBit j with
    | false => rfl
    | true =>
      rcases mem_tri_iff.mp hbit with h | h | h
      exacts [absurd h h1, absurd h h2, absurd h h3]
  -- the four cubics at the apex `c`
  have m1 : tri a b c ∈ supp 11 N c :=
    mem_supp.mpr ⟨tri_lt ha hb hcn, mem_tri_iff.mpr (Or.inr (Or.inr rfl)), hNabc⟩
  have m2 : tri a wa c ∈ supp 11 N c :=
    mem_supp.mpr ⟨tri_lt ha hwan hcn, mem_tri_iff.mpr (Or.inr (Or.inr rfl)), hNawac⟩
  have m3 : tri b wb c ∈ supp 11 N c :=
    mem_supp.mpr ⟨tri_lt hb hwbn hcn, mem_tri_iff.mpr (Or.inr (Or.inr rfl)), hNbwbc⟩
  have m4 : tri wa wb c ∈ supp 11 N c :=
    mem_supp.mpr ⟨tri_lt hwan hwbn hcn, mem_tri_iff.mpr (Or.inr (Or.inr rfl)), hNwawbc⟩
  have e12 : tri a b c ≠ tri a wa c := by
    intro h
    have h1 : (tri a b c).testBit b = true := mem_tri_iff.mpr (Or.inr (Or.inl rfl))
    rw [h, htrifalse a wa c b (Ne.symm hab) hbwa hbc] at h1
    simp at h1
  have e13 : tri a b c ≠ tri b wb c := by
    intro h
    have h1 : (tri a b c).testBit a = true := mem_tri_iff.mpr (Or.inl rfl)
    rw [h, htrifalse b wb c a hab hawb hac] at h1
    simp at h1
  have e14 : tri a b c ≠ tri wa wb c := by
    intro h
    have h1 : (tri a b c).testBit a = true := mem_tri_iff.mpr (Or.inl rfl)
    rw [h, htrifalse wa wb c a hawa hawb hac] at h1
    simp at h1
  have e23 : tri a wa c ≠ tri b wb c := by
    intro h
    have h1 : (tri a wa c).testBit a = true := mem_tri_iff.mpr (Or.inl rfl)
    rw [h, htrifalse b wb c a hab hawb hac] at h1
    simp at h1
  have e24 : tri a wa c ≠ tri wa wb c := by
    intro h
    have h1 : (tri a wa c).testBit a = true := mem_tri_iff.mpr (Or.inl rfl)
    rw [h, htrifalse wa wb c a hawa hawb hac] at h1
    simp at h1
  have e34 : tri b wb c ≠ tri wa wb c := by
    intro h
    have h1 : (tri b wb c).testBit b = true := mem_tri_iff.mpr (Or.inl rfl)
    rw [h, htrifalse wa wb c b hbwa hbwb hbc] at h1
    simp at h1
  have hsub : ({tri a b c, tri a wa c, tri b wb c, tri wa wb c} : Finset ℕ) ⊆ supp 11 N c := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [m1, m2, m3, m4]
  have h4card : ({tri a b c, tri a wa c, tri b wb c, tri wa wb c} : Finset ℕ).card = 4 := by
    rw [card_insert_of_notMem (by simp [e12, e13, e14]),
      card_insert_of_notMem (by simp [e23, e24]), card_pair e34]
  have hsuppeq : ({tri a b c, tri a wa c, tri b wb c, tri wa wb c} : Finset ℕ) = supp 11 N c :=
    eq_of_subset_of_card_le hsub (by rw [h4card, mass_four_card hsol hcn (hm c hcn)])
  have Hc : ∀ S, S < 2 ^ 11 → N S ≠ 0 → S.testBit c = true →
      S = tri a b c ∨ S = tri a wa c ∨ S = tri b wb c ∨ S = tri wa wb c := by
    intro S hS hNS hSb
    have : S ∈ ({tri a b c, tri a wa c, tri b wb c, tri wa wb c} : Finset ℕ) := by
      rw [hsuppeq]; exact mem_supp.mpr ⟨hS, hSb, hNS⟩
    simpa only [mem_insert, mem_singleton] using this
  -- no support set crosses out of `{a, b, wa, wb, c}`
  have hcross : ∀ S, S < 2 ^ 11 → N S ≠ 0 →
      (∀ j, S.testBit j = true → j ∈ ({a, b, wa, wb, c} : Finset ℕ)) ∨
      (∀ j, S.testBit j = true → j ∉ ({a, b, wa, wb, c} : Finset ℕ)) := by
    intro S hS hNS
    by_cases hout : ∀ j, S.testBit j = true → j ∉ ({a, b, wa, wb, c} : Finset ℕ)
    · exact Or.inr hout
    left
    push_neg at hout
    obtain ⟨j, hj, hjA⟩ := hout
    simp only [mem_insert, mem_singleton] at hjA
    have key : S = pair a b ∨ S = pair a wa ∨ S = pair b wb ∨ S = pair wa wb ∨
        S = tri a b c ∨ S = tri a wa c ∨ S = tri b wb c ∨ S = tri wa wb c := by
      rcases hjA with h0 | h0 | h0 | h0 | h0
      · rw [h0] at hj
        rcases Ha S hS hNS hj with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · rw [h0] at hj
        rcases Hb S hS hNS hj with h | h | h | h
        · exact Or.inl (by rw [h]; exact pair_comm b a)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [h]; exact (tri_swap a b c).symm)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · rw [h0] at hj
        rcases Hwa S hS hNS hj with h | h | h | h
        · exact Or.inr (Or.inl (by rw [h]; exact pair_comm wa a))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl (by rw [h]; exact (tri_swap a wa c).symm))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
      · rw [h0] at hj
        rcases Hwb S hS hNS hj with h | h | h | h
        · exact Or.inr (Or.inr (Or.inl (by rw [h]; exact pair_comm wb b)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h]; exact pair_comm wb wa))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl (by rw [h]; exact (tri_swap b wb c).symm)))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (by rw [h]; exact (tri_swap wa wb c).symm)))))))
      · rw [h0] at hj
        rcases Hc S hS hNS hj with h | h | h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
    intro k hk
    simp only [mem_insert, mem_singleton]
    rcases key with h | h | h | h | h | h | h | h <;> rw [h] at hk
    · have h' := mem_pair_iff.mp hk; omega
    · have h' := mem_pair_iff.mp hk; omega
    · have h' := mem_pair_iff.mp hk; omega
    · have h' := mem_pair_iff.mp hk; omega
    · have h' := mem_tri_iff.mp hk; omega
    · have h' := mem_tri_iff.mp hk; omega
    · have h' := mem_tri_iff.mp hk; omega
    · have h' := mem_tri_iff.mp hk; omega
  -- five of the eleven vertices are closed, so some support set lies wholly outside
  have hA5 : ({a, b, wa, wb, c} : Finset ℕ).card = 5 := by
    rw [card_insert_of_notMem (by simp [hab, hawa, hawb, hac]),
      card_insert_of_notMem (by simp [hbwa, hbwb, hbc]),
      card_insert_of_notMem (by simp [hwawb, hwac]), card_pair hwbc]
  have hAsub : ({a, b, wa, wb, c} : Finset ℕ) ⊆ range 11 := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_range]
    rcases hx with h | h | h | h | h <;> omega
  have hss : ({a, b, wa, wb, c} : Finset ℕ) ⊂ range 11 := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hAsub, ?_⟩
    intro h
    rw [h, card_range] at hA5
    omega
  obtain ⟨w, hwr, hwA⟩ := Finset.exists_of_ssubset hss
  obtain ⟨T0, hT0lt, hT0bit, hT0N⟩ := hsol.2.2.2 w (mem_range.mp hwr)
  have hS0bit : (pair a b).testBit a = true := mem_pair_iff.mpr (Or.inl rfl)
  have hS0A : ∀ j, (pair a b).testBit j = true → j ∈ ({a, b, wa, wb, c} : Finset ℕ) := by
    intro j hj
    have h' := mem_pair_iff.mp hj
    simp only [mem_insert, mem_singleton]
    omega
  have hT0A : ∀ j, T0.testBit j = true → j ∉ ({a, b, wa, wb, c} : Finset ℕ) := by
    rcases hcross T0 hT0lt hT0N with h | h
    · exact absurd (h w hT0bit) hwA
    · exact h
  exact no_crossing_split hsol (pair_lt_two_pow ha hb) hNab hS0bit hS0A hT0lt hT0N hT0bit
    hT0A hcross

/-- **The `{1,1,1,1}` sub-case of δ = 4 is impossible.**  The four quadratics form a 4-cycle
`a-b-wb-wa-a`; each cycle vertex has an L3 link whose two cubics run through one apex, all
four apexes coincide at a vertex `c`, and `eleven_cycle_closed` finishes. -/
theorem eleven_four_quadratics {N : ℕ → ℤ} (hsol : IsSol 11 N)
    (hm : ∀ v, v < 11 → mass 11 N v = 4)
    {Q1 Q2 Q3 Q4 : ℕ} (d12 : Q1 ≠ Q2) (d13 : Q1 ≠ Q3) (d14 : Q1 ≠ Q4)
    (d23 : Q2 ≠ Q3) (d24 : Q2 ≠ Q4) (d34 : Q3 ≠ Q4)
    (hQ : ∀ Q ∈ ({Q1, Q2, Q3, Q4} : Finset ℕ), Q < 2 ^ 11 ∧ N Q ≠ 0 ∧ card 11 Q = 2)
    (hall : ∀ S, S < 2 ^ 11 → N S ≠ 0 → S = Q1 ∨ S = Q2 ∨ S = Q3 ∨ S = Q4 ∨ card 11 S = 3) :
    False := by
  have hQcard : ({Q1, Q2, Q3, Q4} : Finset ℕ).card = 4 := by
    rw [card_insert_of_notMem (by simp [d12, d13, d14]),
      card_insert_of_notMem (by simp [d23, d24]), card_pair d34]
  have hnolin : ∀ i, i < 11 → N (2 ^ i) = 0 := by
    intro i hi
    by_contra hne
    have hlt : (2 : ℕ) ^ i < 2 ^ 11 := Nat.pow_lt_pow_right (by norm_num) hi
    have hc1 : card 11 (2 ^ i) = 1 := card_two_pow hi
    rcases hall _ hlt hne with h | h | h | h | h
    · have h2 := (hQ Q1 (by simp)).2.2; rw [← h] at h2; omega
    · have h2 := (hQ Q2 (by simp)).2.2; rw [← h] at h2; omega
    · have h2 := (hQ Q3 (by simp)).2.2; rw [← h] at h2; omega
    · have h2 := (hQ Q4 (by simp)).2.2; rw [← h] at h2; omega
    · omega
  have hquad_mem : ∀ u t, u < 11 → t < 11 → u ≠ t → N (pair u t) ≠ 0 →
      pair u t ∈ ({Q1, Q2, Q3, Q4} : Finset ℕ) := by
    intro u t hu ht hut hN
    have hlt := pair_lt_two_pow hu ht
    have hc : card 11 (pair u t) = 2 := card_pair_eq hu ht hut
    rcases hall _ hlt hN with h | h | h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
    · simp [h]
    · omega
  obtain ⟨a, b, ha, hb, hab, hQ1eq⟩ :=
    exists_pair_of_card_two (hQ Q1 (by simp)).1 (hQ Q1 (by simp)).2.2
  have hNab : N (pair a b) ≠ 0 := by rw [← hQ1eq]; exact (hQ Q1 (by simp)).2.1
  have hNba : N (pair b a) ≠ 0 := by rwa [pair_comm]
  obtain ⟨wa, ra, hwan, hran, hwab, hwara, hbra, hwaa, hraa, hNawa, hNabra, hNawara, Ha⟩ :=
    link_L3' hsol ha (hm a ha) (hnolin a ha) hb (Ne.symm hab) hNab
  obtain ⟨wb, rb, hwbn, hrbn, hwba, hwbrb, harb, hwbb, hrbb, hNbwb, hNbarb, hNbwbrb, Hb⟩ :=
    link_L3' hsol hb (hm b hb) (hnolin b hb) ha hab hNba
  have hrr : ra = rb :=
    apex_eq ha hb hran hraa (Ne.symm hbra) hab hwba (Ne.symm harb) hNabra Hb
  subst hrr
  have hNwaa : N (pair wa a) ≠ 0 := by rw [pair_comm]; exact hNawa
  obtain ⟨w2, rwa, hw2n, hrwan, hw2a, hw2rwa, harwa, hw2wa, hrwawa, hNwaw2, hNwaarwa,
    hNwaw2rwa, Hwa⟩ :=
    link_L3' hsol hwan (hm wa hwan) (hnolin wa hwan) ha (Ne.symm hwaa) hNwaa
  have hrwa : ra = rwa :=
    apex_eq ha hwan hran hraa (Ne.symm hwara) (Ne.symm hwaa) hw2a (Ne.symm harwa)
      hNawara Hwa
  subst hrwa
  have hNwbb : N (pair wb b) ≠ 0 := by rw [pair_comm]; exact hNbwb
  obtain ⟨w3, rwb, hw3n, hrwbn, hw3b, hw3rwb, hbrwb, hw3wb, hrwbwb, hNwbw3, hNwbbrwb,
    hNwbw3rwb, Hwb⟩ :=
    link_L3' hsol hwbn (hm wb hwbn) (hnolin wb hwbn) hb (Ne.symm hwbb) hNwbb
  have hrwb : ra = rwb :=
    apex_eq hb hwbn hran hrbb (Ne.symm hwbrb) (Ne.symm hwbb) hw3b (Ne.symm hbrwb)
      hNbwbrb Hwb
  subst hrwb
  have hP1P2 : pair a b ≠ pair a wa := by
    intro h
    rcases pair_eq_iff.mp h with ⟨-, h'⟩ | ⟨h', -⟩
    · exact hwab h'.symm
    · exact hwaa h'.symm
  have hP1P3 : pair a b ≠ pair b wb := by
    intro h
    rcases pair_eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
    · exact hab h'
    · exact hwba h'.symm
  have hP2P3 : pair a wa ≠ pair b wb := by
    intro h
    rcases pair_eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
    · exact hab h'
    · exact hwba h'.symm
  have hMP1 := hquad_mem a b ha hb hab hNab
  have hMP2 := hquad_mem a wa ha hwan (Ne.symm hwaa) hNawa
  have hMP3 := hquad_mem b wb hb hwbn (Ne.symm hwbb) hNbwb
  have hMPwa := hquad_mem wa w2 hwan hw2n (Ne.symm hw2wa) hNwaw2
  have hMPwb := hquad_mem wb w3 hwbn hw3n (Ne.symm hw3wb) hNwbw3
  have hsub3 : ({pair a b, pair a wa, pair b wb} : Finset ℕ) ⊆ ({Q1, Q2, Q3, Q4} : Finset ℕ) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with h | h | h
    · rw [h]; exact hMP1
    · rw [h]; exact hMP2
    · rw [h]; exact hMP3
  -- the quadratic graph has no triangle, so `wa ≠ wb`
  have hwawb : wa ≠ wb := by
    intro hEq
    have hbitwa : (pair b wb).testBit wa = true := mem_pair_iff.mpr (Or.inr hEq)
    have hcP3 : card 11 (pair b wb) = 2 := card_pair_eq hb hwbn (Ne.symm hwbb)
    have hw2b : w2 = b := by
      rcases Hwa _ (pair_lt_two_pow hb hwbn) hNbwb hbitwa with h | h | h | h
      · rcases pair_eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
        · exact absurd h'.symm hwab
        · exact absurd h'.symm hab
      · rcases pair_eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
        · exact absurd h'.symm hwab
        · exact h'.symm
      · rw [h, card_tri_eq hwan ha hran hwaa hwara (Ne.symm hraa)] at hcP3; omega
      · rw [h, card_tri_eq hwan hw2n hran (Ne.symm hw2wa) hwara hw2rwa] at hcP3; omega
    obtain ⟨P4, hP4Q, hP4a, hP4b, hP4c⟩ :=
      exists_fourth hP1P2 hP1P3 hP2P3 hsub3 hQcard
    obtain ⟨hP4lt, hP4N, hP4c2⟩ := hQ P4 hP4Q
    have hnoa : P4.testBit a = false := by
      cases hcon : P4.testBit a with
      | false => rfl
      | true =>
        exfalso
        rcases Ha _ hP4lt hP4N hcon with h | h | h | h
        · exact hP4a h
        · exact hP4b h
        · rw [h, card_tri_eq ha hb hran hab (Ne.symm hraa) hbra] at hP4c2; omega
        · rw [h, card_tri_eq ha hwan hran (Ne.symm hwaa) (Ne.symm hraa) hwara] at hP4c2; omega
    have hnob : P4.testBit b = false := by
      cases hcon : P4.testBit b with
      | false => rfl
      | true =>
        exfalso
        rcases Hb _ hP4lt hP4N hcon with h | h | h | h
        · exact hP4a (by rw [h]; exact pair_comm b a)
        · exact hP4c h
        · rw [h, card_tri_eq hb ha hran (Ne.symm hab) (Ne.symm hrbb) (Ne.symm hraa)] at hP4c2
          omega
        · rw [h, card_tri_eq hb hwbn hran (Ne.symm hwbb) (Ne.symm hrbb) hwbrb] at hP4c2
          omega
    have hnowa : P4.testBit wa = false := by
      cases hcon : P4.testBit wa with
      | false => rfl
      | true =>
        exfalso
        rcases Hwa _ hP4lt hP4N hcon with h | h | h | h
        · exact hP4b (by rw [h]; exact pair_comm wa a)
        · exact hP4c (by rw [h, hw2b, pair_comm wa b, hEq])
        · rw [h, card_tri_eq hwan ha hran hwaa hwara (Ne.symm hraa)] at hP4c2; omega
        · rw [h, card_tri_eq hwan hw2n hran (Ne.symm hw2wa) hwara hw2rwa] at hP4c2; omega
    obtain ⟨u, t, hu, ht, hut, hP4eq⟩ := exists_pair_of_card_two hP4lt hP4c2
    have hbu : P4.testBit u = true := by rw [hP4eq]; exact mem_pair_iff.mpr (Or.inl rfl)
    have hua : u ≠ a := by intro h; rw [h, hnoa] at hbu; simp at hbu
    have hub : u ≠ b := by intro h; rw [h, hnob] at hbu; simp at hbu
    have huwa : u ≠ wa := by intro h; rw [h, hnowa] at hbu; simp at hbu
    have huwb : u ≠ wb := by rw [← hEq]; exact huwa
    have hNut : N (pair u t) ≠ 0 := by rw [← hP4eq]; exact hP4N
    obtain ⟨w4, r4, hw4n, -, hw4t, -, -, hw4u, -, hNuw4, -, -, -⟩ :=
      link_L3' hsol hu (hm u hu) (hnolin u hu) ht (Ne.symm hut) hNut
    have hbu5 : (pair u w4).testBit u = true := mem_pair_iff.mpr (Or.inl rfl)
    refine five_in_four (P5 := pair u w4) (Q1 := Q1) (Q2 := Q2) (Q3 := Q3) (Q4 := Q4)
      hP1P2 hP1P3 (Ne.symm hP4a) ?_ hP2P3 (Ne.symm hP4b) ?_ (Ne.symm hP4c) ?_ ?_ ?_
    · intro h
      have hx : (pair a b).testBit u = true := by rw [h]; exact hbu5
      rcases mem_pair_iff.mp hx with h' | h'
      · exact hua h'
      · exact hub h'
    · intro h
      have hx : (pair a wa).testBit u = true := by rw [h]; exact hbu5
      rcases mem_pair_iff.mp hx with h' | h'
      · exact hua h'
      · exact huwa h'
    · intro h
      have hx : (pair b wb).testBit u = true := by rw [h]; exact hbu5
      rcases mem_pair_iff.mp hx with h' | h'
      · exact hub h'
      · exact huwb h'
    · intro h
      rw [hP4eq] at h
      rcases pair_eq_iff.mp h with ⟨-, h'⟩ | ⟨-, h'⟩
      · exact hw4t h'.symm
      · exact hut h'.symm
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with h | h | h | h | h
      · rw [h]; exact hMP1
      · rw [h]; exact hMP2
      · rw [h]; exact hMP3
      · rw [h]; exact hP4Q
      · rw [h]; exact hquad_mem u w4 hu hw4n (Ne.symm hw4u) hNuw4
  -- the fourth quadratic is `{wa, wb}`
  have hPwa1 : pair wa w2 ≠ pair a b := by
    intro h
    have hx : (pair a b).testBit wa = true := by rw [← h]; exact mem_pair_iff.mpr (Or.inl rfl)
    rcases mem_pair_iff.mp hx with h' | h'
    · exact hwaa h'
    · exact hwab h'
  have hPwa2 : pair wa w2 ≠ pair a wa := by
    intro h
    rcases pair_eq_iff.mp h with ⟨h', -⟩ | ⟨-, h'⟩
    · exact hwaa h'
    · exact hw2a h'
  have hPwa3 : pair wa w2 ≠ pair b wb := by
    intro h
    rcases pair_eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
    · exact hwab h'
    · exact hwawb h'
  have hPwb1 : pair wb w3 ≠ pair a b := by
    intro h
    have hx : (pair a b).testBit wb = true := by rw [← h]; exact mem_pair_iff.mpr (Or.inl rfl)
    rcases mem_pair_iff.mp hx with h' | h'
    · exact hwba h'
    · exact hwbb h'
  have hPwb2 : pair wb w3 ≠ pair a wa := by
    intro h
    rcases pair_eq_iff.mp h with ⟨h', -⟩ | ⟨h', -⟩
    · exact hwba h'
    · exact hwawb h'.symm
  have hPwb3 : pair wb w3 ≠ pair b wb := by
    intro h
    rcases pair_eq_iff.mp h with ⟨h', -⟩ | ⟨-, h'⟩
    · exact hwbb h'
    · exact hw3b h'
  have hPeq : pair wa w2 = pair wb w3 := by
    by_contra hne
    refine five_in_four (Q1 := Q1) (Q2 := Q2) (Q3 := Q3) (Q4 := Q4)
      hP1P2 hP1P3 (Ne.symm hPwa1) (Ne.symm hPwb1) hP2P3 (Ne.symm hPwa2)
      (Ne.symm hPwb2) (Ne.symm hPwa3) (Ne.symm hPwb3) hne ?_
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with h | h | h | h | h
    · rw [h]; exact hMP1
    · rw [h]; exact hMP2
    · rw [h]; exact hMP3
    · rw [h]; exact hMPwa
    · rw [h]; exact hMPwb
  have hw2wb : w2 = wb := by
    rcases pair_eq_iff.mp hPeq with ⟨h', -⟩ | ⟨-, h'⟩
    · exact absurd h' hwawb
    · exact h'
  have hw3wa : w3 = wa := by
    rcases pair_eq_iff.mp hPeq with ⟨h', -⟩ | ⟨h', -⟩
    · exact absurd h' hwawb
    · exact h'.symm
  refine eleven_cycle_closed hsol hm ha hb hwan hwbn hran hab (Ne.symm hwaa) (Ne.symm hwba)
    (Ne.symm hraa) (Ne.symm hwab) (Ne.symm hwbb) hbra hwawb hwara hwbrb
    hNab hNabra hNawara hNbwbrb (by rw [← hw2wb]; exact hNwaw2rwa) Ha Hb ?_ ?_
  · intro S h1 h2 h3
    rw [← hw2wb]
    exact Hwa S h1 h2 h3
  · intro S h1 h2 h3
    rw [← hw3wa]
    exact Hwb S h1 h2 h3

/-- **`δ = 4` is reduced to the `{2,2}` sub-case.**  If every vertex of an 11-variable
solution has mass 4, then the solution has exactly two linear terms `{i}` and `{j}`, no
quadratic and no constant term, and every other support set is a triple.  (Whether *that*
configuration can exist is the one remaining sub-case of "Case delta = 4" of
R3_equals_10.md; see `lean/HANDOFF.md`, Step C.) -/
theorem delta_four_two_linear {N : ℕ → ℤ} (hsol : IsSol 11 N)
    (hm : ∀ v, v < 11 → mass 11 N v = 4) :
    ∃ i j, i < 11 ∧ j < 11 ∧ i ≠ j ∧ N (2 ^ i) ≠ 0 ∧ N (2 ^ j) ≠ 0 ∧
      ∀ S, S < 2 ^ 11 → N S ≠ 0 → S = 2 ^ i ∨ S = 2 ^ j ∨ card 11 S = 3 := by
  rcases delta_four_structure hsol hm with h |
    ⟨Q1, Q2, Q3, Q4, e12, e13, e14, e23, e24, e34, hQ, hall⟩
  · exact h
  · exact (eleven_four_quadratics hsol hm e12 e13 e14 e23 e24 e34 hQ hall).elim

/-! ## The `{2,2}` sub-case of δ = 4: two linear terms

`delta_four_two_linear` leaves exactly this configuration: linear terms `{i}` and `{j}`, no
quadratic and no constant term, every other support set a cubic.  The vertices `i` and `j`
then have L4 links (a triangle), every other vertex has an L1 link (a 4-cycle), and the
argument of `R3_equals_10.md` closes a five-element set `{i, j, a, b, c}`. -/

/-- the two endpoints of a pair are determined by the pair -/
lemma pair_mem_of_eq {x y u w : ℕ} (h : pair x y = pair u w) :
    (x = u ∨ x = w) ∧ (y = u ∨ y = w) := by
  constructor
  · have hx : (pair x y).testBit x = true := mem_pair_iff.mpr (Or.inl rfl)
    rw [h] at hx; exact mem_pair_iff.mp hx
  · have hy : (pair x y).testBit y = true := mem_pair_iff.mpr (Or.inr rfl)
    rw [h] at hy; exact mem_pair_iff.mp hy

/-- two distinct vertices of a triangle span one of its three edges -/
lemma pair_of_triangle {x y a b c : ℕ} (hxy : x ≠ y)
    (hx : x = a ∨ x = b ∨ x = c) (hy : y = a ∨ y = b ∨ y = c) :
    pair x y = pair a b ∨ pair x y = pair b c ∨ pair x y = pair a c := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact absurd rfl hxy
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl (pair_comm _ _)
  · exact absurd rfl hxy
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (pair_comm _ _))
  · exact Or.inr (Or.inl (pair_comm _ _))
  · exact absurd rfl hxy

/-- **L4.**  A mass-4 vertex carrying a linear term and no quadratic term has a triangle
link: the cubics through `v` are exactly the `{v, x, y}` with `{x, y}` a 2-subset of a
triangle `{a, b, c}`. -/
theorem link_L4_of_linear {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n)
    (h4 : mass n N v = 4) (hlin : N (2 ^ v) ≠ 0)
    (hnoquad : ∀ y, y < n → y ≠ v → N (pair v y) = 0) :
    ∃ a b c, a < n ∧ b < n ∧ c < n ∧ a ≠ v ∧ b ≠ v ∧ c ≠ v ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ∀ x y, x < n → y < n → x ≠ v → y ≠ v →
        (N (tri v x y) ≠ 0 ↔
          (x ≠ y ∧ (x = a ∨ x = b ∨ x = c) ∧ (y = a ∨ y = b ∨ y = c))) := by
  have h0 : (0 : ℕ) ∈ link n N v := (zero_mem_link hv).mpr hlin
  rcases mass_four_link_cover hsol hv h4 with
    ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, hL⟩ | ⟨x, y, hxy, hL⟩ |
    ⟨x, y, z, hxy, hxz, hyz, hL⟩ | ⟨x, y, z, hxy, hxz, hyz, hL⟩
  · exfalso
    rw [hL] at h0
    simp only [mem_insert, mem_singleton] at h0
    rcases h0 with h | h | h | h <;> exact pair_ne_zero h.symm
  · exfalso
    have hmem : (2 : ℕ) ^ x ∈ link n N v := by rw [hL]; simp
    obtain ⟨hxn, hxv, hq⟩ := link_two_pow hv hmem
    exact hq (hnoquad x hxn hxv)
  · exfalso
    have hmem : (2 : ℕ) ^ x ∈ link n N v := by rw [hL]; simp
    obtain ⟨hxn, hxv, hq⟩ := link_two_pow hv hmem
    exact hq (hnoquad x hxn hxv)
  · -- L4: the link is `{0, pair x y, pair y z, pair x z}`
    have m1 : pair x y ∈ link n N v := by rw [hL]; simp
    have m2 : pair y z ∈ link n N v := by rw [hL]; simp
    have m3 : pair x z ∈ link n N v := by rw [hL]; simp
    obtain ⟨hxn, hyn, hxv, hyv, -⟩ := link_pair hv m1
    obtain ⟨-, hzn, -, hzv, -⟩ := link_pair hv m2
    refine ⟨x, y, z, hxn, hyn, hzn, hxv, hyv, hzv, hxy, hxz, hyz, ?_⟩
    intro u t hu ht huv htv
    constructor
    · intro hN
      have hmem : pair u t ∈ link n N v := (pair_mem_link hv hu ht huv htv).mpr hN
      rw [hL] at hmem
      simp only [mem_insert, mem_singleton] at hmem
      have hut : u ≠ t := by
        rintro rfl
        have : pair u u = 2 ^ u := by
          apply Nat.eq_of_testBit_eq; intro k
          rw [testBit_pair, Nat.testBit_two_pow]
          by_cases h : u = k <;> simp [h]
        rcases hmem with h | h | h | h
        · exact pair_ne_zero h
        · exact pair_ne_two_pow hxy (by rw [← h, this])
        · exact pair_ne_two_pow hyz (by rw [← h, this])
        · exact pair_ne_two_pow hxz (by rw [← h, this])
      refine ⟨hut, ?_, ?_⟩
      · rcases hmem with h | h | h | h
        · exact absurd h pair_ne_zero
        · have := (pair_mem_of_eq h).1; tauto
        · have := (pair_mem_of_eq h).1; tauto
        · have := (pair_mem_of_eq h).1; tauto
      · rcases hmem with h | h | h | h
        · exact absurd h pair_ne_zero
        · have := (pair_mem_of_eq h).2; tauto
        · have := (pair_mem_of_eq h).2; tauto
        · have := (pair_mem_of_eq h).2; tauto
    · rintro ⟨hut, hu3, ht3⟩
      have hmem : pair u t ∈ link n N v := by
        rw [hL]
        rcases pair_of_triangle hut hu3 ht3 with h | h | h <;> rw [h] <;> simp
      exact (pair_mem_link hv hu ht huv htv).mp hmem

/-- a `{2,2}` configuration has no quadratic term at all -/
lemma two_linear_no_quad {N : ℕ → ℤ} {i j : ℕ}
    (hall : ∀ S, S < 2 ^ 11 → N S ≠ 0 → S = 2 ^ i ∨ S = 2 ^ j ∨ card 11 S = 3)
    {u w : ℕ} (hu : u < 11) (hw : w < 11) (huw : u ≠ w) : N (pair u w) = 0 := by
  by_contra hne
  rcases hall _ (pair_lt_two_pow hu hw) hne with h | h | h
  · exact pair_ne_two_pow huw h
  · exact pair_ne_two_pow huw h
  · rw [card_pair_eq hu hw huw] at h; omega

/-- with only the two linear terms below the top level, every other vertex is cubic -/
lemma cubicAt_of_two_linear {N : ℕ → ℤ} {i j : ℕ}
    (hall : ∀ S, S < 2 ^ 11 → N S ≠ 0 → S = 2 ^ i ∨ S = 2 ^ j ∨ card 11 S = 3)
    {v : ℕ} (hvi : v ≠ i) (hvj : v ≠ j) : CubicAt 11 N v := by
  intro S hS hN hb
  rcases hall S hS hN with rfl | rfl | h3
  · exact absurd (by
      by_contra hne
      rw [Nat.testBit_two_pow_of_ne (Ne.symm hne)] at hb
      exact Bool.false_ne_true hb : v = i) hvi
  · exact absurd (by
      by_contra hne
      rw [Nat.testBit_two_pow_of_ne (Ne.symm hne)] at hb
      exact Bool.false_ne_true hb : v = j) hvj
  · exact h3

/-- a set of vertices each of whose cubics stays inside it, and which contains every
non-cubic support set, is closed. -/
lemma closure_local {n : ℕ} {N : ℕ → ℤ} {A : Finset ℕ}
    (hlow : ∀ S, S < 2 ^ n → N S ≠ 0 → card n S ≠ 3 → ∀ k, S.testBit k = true → k ∈ A)
    (hclosed : ∀ u ∈ A, ∀ x y, x < n → y < n → x ≠ u → y ≠ u → N (tri u x y) ≠ 0 →
      x ∈ A ∧ y ∈ A) :
    ∀ S, S < 2 ^ n → N S ≠ 0 →
      (∀ k, S.testBit k = true → k ∈ A) ∨ (∀ k, S.testBit k = true → k ∉ A) := by
  intro S hS hN
  by_cases h3 : card n S = 3
  · obtain ⟨x1, x2, x3, hx1, hx2, hx3, hn12, hn13, hn23, rfl⟩ :=
      exists_tri_of_card_three hS h3
    by_cases hc1 : x1 ∈ A
    · left
      obtain ⟨m2, m3⟩ := hclosed x1 hc1 x2 x3 hx2 hx3 (Ne.symm hn12) (Ne.symm hn13) hN
      intro k hk; rcases mem_tri_iff.mp hk with rfl | rfl | rfl <;> assumption
    by_cases hc2 : x2 ∈ A
    · left
      have hN2 : N (tri x2 x1 x3) ≠ 0 := by rw [← tri_swap x1 x2 x3]; exact hN
      obtain ⟨m1, m3⟩ := hclosed x2 hc2 x1 x3 hx1 hx3 hn12 (Ne.symm hn23) hN2
      intro k hk; rcases mem_tri_iff.mp hk with rfl | rfl | rfl <;> assumption
    by_cases hc3 : x3 ∈ A
    · left
      have hN3 : N (tri x3 x1 x2) ≠ 0 := by rw [← tri_rotr x1 x2 x3]; exact hN
      obtain ⟨m1, m2⟩ := hclosed x3 hc3 x1 x2 hx1 hx2 hn13 hn23 hN3
      intro k hk; rcases mem_tri_iff.mp hk with rfl | rfl | rfl <;> assumption
    · right; intro k hk; rcases mem_tri_iff.mp hk with rfl | rfl | rfl <;> assumption
  · exact Or.inl (hlow S hS hN h3)

/-- three distinct vertices inside a triangle exhaust it -/
lemma mem_of_triangle_eq {p q r a b c x : ℕ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a = p ∨ a = q ∨ a = r) (hb : b = p ∨ b = q ∨ b = r) (hc : c = p ∨ c = q ∨ c = r)
    (hx : x = p ∨ x = q ∨ x = r) : x = a ∨ x = b ∨ x = c := by
  omega

/-- If the second linear vertex `a` were a vertex of the triangle link of the first linear
vertex `i`, the mass-4 vertex `b` would carry a triangle in its 4-cycle link. -/
lemma linear_not_triangle {N : ℕ → ℤ} (hsol : IsSol 11 N) {i a b c : ℕ}
    (hi : i < 11) (ha : a < 11) (hb : b < 11) (hc : c < 11)
    (hai : a ≠ i) (hbi : b ≠ i) (hci : c ≠ i)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h4a : mass 11 N a = 4) (h4b : mass 11 N b = 4)
    (hlin : N (2 ^ a) ≠ 0)
    (hnoquad : ∀ u w, u < 11 → w < 11 → u ≠ w → N (pair u w) = 0)
    (hcubb : CubicAt 11 N b)
    (F1 : N (tri i a b) ≠ 0) (F2 : N (tri i b c) ≠ 0) (F3 : N (tri i a c) ≠ 0) : False := by
  obtain ⟨p, q, r, -, -, -, -, -, -, -, -, -, H⟩ :=
    link_L4_of_linear hsol ha h4a hlin (fun y hy hya => hnoquad a y ha hy (Ne.symm hya))
  have k1 := (H i b hi hb (Ne.symm hai) (Ne.symm hab)).mp
    (by rw [show tri a i b = tri i a b from tri_ext (fun _ => by omega)]; exact F1)
  have k2 := (H i c hi hc (Ne.symm hai) (Ne.symm hac)).mp
    (by rw [show tri a i c = tri i a c from tri_ext (fun _ => by omega)]; exact F3)
  have Fbc : N (tri a b c) ≠ 0 :=
    (H b c hb hc (Ne.symm hab) (Ne.symm hac)).mpr ⟨hbc, k1.2.2, k2.2.2⟩
  exact no_triangle_at' hsol hcubb hb hi ha hc h4b (Ne.symm hbi) hab (Ne.symm hbc) hac
    (by rw [show tri b i a = tri i a b from tri_ext (fun _ => by omega)]; exact F1)
    (by rw [show tri b i c = tri i b c from tri_ext (fun _ => by omega)]; exact F2)
    (by rw [show tri b a c = tri a b c from tri_ext (fun _ => by omega)]; exact Fbc)

set_option maxHeartbeats 1000000 in
/-- **The `{2,2}` sub-case of δ = 4 is impossible**, and with it the whole case `δ = 4`:
at `n = 11` a solution cannot have all eleven masses equal to 4. -/
theorem eleven_delta_four {N : ℕ → ℤ} (hsol : IsSol 11 N)
    (hm : ∀ v, v < 11 → mass 11 N v = 4) : False := by
  obtain ⟨i, j, hi, hj, hij, hNi, hNj, hall⟩ := delta_four_two_linear hsol hm
  have hnoquad : ∀ u w, u < 11 → w < 11 → u ≠ w → N (pair u w) = 0 :=
    fun u w hu hw huw => two_linear_no_quad hall hu hw huw
  -- the L4 (triangle) link at `i`
  obtain ⟨a, b, c, ha, hb, hc, hai, hbi, hci, hab, hac, hbc, Hi⟩ :=
    link_L4_of_linear hsol hi (hm i hi) hNi (fun y hy hyi => hnoquad i y hi hy (Ne.symm hyi))
  have Fiab : N (tri i a b) ≠ 0 :=
    (Hi a b ha hb hai hbi).mpr ⟨hab, Or.inl rfl, Or.inr (Or.inl rfl)⟩
  have Fibc : N (tri i b c) ≠ 0 :=
    (Hi b c hb hc hbi hci).mpr ⟨hbc, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
  have Fiac : N (tri i a c) ≠ 0 :=
    (Hi a c ha hc hai hci).mpr ⟨hac, Or.inl rfl, Or.inr (Or.inr rfl)⟩
  -- `j` is none of the triangle vertices
  have hja : j ≠ a := fun h =>
    linear_not_triangle hsol hi ha hb hc hai hbi hci hab hac hbc (hm a ha) (hm b hb)
      (h ▸ hNj) hnoquad
      (cubicAt_of_two_linear hall hbi (fun hbj => hab (h.symm.trans hbj.symm)))
      Fiab Fibc Fiac
  have hjb : j ≠ b := fun h =>
    linear_not_triangle hsol hi hb ha hc hbi hai hci (Ne.symm hab) hbc hac (hm b hb) (hm a ha)
      (h ▸ hNj) hnoquad
      (cubicAt_of_two_linear hall hai (fun haj => hab (haj.trans h)))
      (by rw [show tri i b a = tri i a b from tri_ext (fun _ => by omega)]; exact Fiab)
      Fiac Fibc
  have hjc : j ≠ c := fun h =>
    linear_not_triangle hsol hi hc ha hb hci hai hbi (Ne.symm hac) (Ne.symm hbc) hab
      (hm c hc) (hm a ha) (h ▸ hNj) hnoquad
      (cubicAt_of_two_linear hall hai (fun haj => hac (haj.trans h)))
      (by rw [show tri i c a = tri i a c from tri_ext (fun _ => by omega)]; exact Fiac)
      Fiab
      (by rw [show tri i c b = tri i b c from tri_ext (fun _ => by omega)]; exact Fibc)
  -- the three triangle vertices are cubic, so their links are 4-cycles through `i`
  have ca : CubicAt 11 N a := cubicAt_of_two_linear hall hai (Ne.symm hja)
  have cb : CubicAt 11 N b := cubicAt_of_two_linear hall hbi (Ne.symm hjb)
  have cc : CubicAt 11 N c := cubicAt_of_two_linear hall hci (Ne.symm hjc)
  obtain ⟨w, hw, hwa, hwi, hwb, hwc, Ha⟩ :=
    link_sixth' hsol ca ha hi hb hc (hm a ha) (Ne.symm hai) (Ne.symm hab) (Ne.symm hac) hbc
      (by rw [show tri a i b = tri i a b from tri_ext (fun _ => by omega)]; exact Fiab)
      (by rw [show tri a i c = tri i a c from tri_ext (fun _ => by omega)]; exact Fiac)
  obtain ⟨w2, hw2, hw2b, hw2i, hw2a, hw2c, Hb⟩ :=
    link_sixth' hsol cb hb hi ha hc (hm b hb) (Ne.symm hbi) hab (Ne.symm hbc) hac
      (by rw [show tri b i a = tri i a b from tri_ext (fun _ => by omega)]; exact Fiab)
      (by rw [show tri b i c = tri i b c from tri_ext (fun _ => by omega)]; exact Fibc)
  obtain ⟨w3, hw3, hw3c, hw3i, hw3a, hw3b, Hc⟩ :=
    link_sixth' hsol cc hc hi ha hb (hm c hc) (Ne.symm hci) hac hbc hab
      (by rw [show tri c i a = tri i a c from tri_ext (fun _ => by omega)]; exact Fiac)
      (by rw [show tri c i b = tri i b c from tri_ext (fun _ => by omega)]; exact Fibc)
  -- the two cubics at `a` through the sixth vertex
  have Facw : N (tri a c w) ≠ 0 := (Ha c w hc hw (Ne.symm hac) hwa).mpr (edge_rs b i c w)
  have Fawb : N (tri a w b) ≠ 0 := (Ha w b hw hb hwa (Ne.symm hab)).mpr (edge_sp b i c w)
  -- the sixth vertices agree
  have hww2 : w = w2 := by
    have hE := (Hb a w ha hw hab hwb).mp
      (by rw [show tri b a w = tri a w b from tri_ext (fun _ => by omega)]; exact Fawb)
    unfold Edge at hE
    clear * - hE hwi hai hac hwc hwa
    omega
  have hww3 : w = w3 := by
    have hE := (Hc a w ha hw hac hwc).mp
      (by rw [show tri c a w = tri a c w from tri_ext (fun _ => by omega)]; exact Facw)
    unfold Edge at hE
    clear * - hE hwi hai hab hwb hwa
    omega
  subst hww2
  subst hww3
  have Fbcw : N (tri b c w) ≠ 0 := (Hb c w hc hw (Ne.symm hbc) hwb).mpr (edge_rs a i c w)
  -- the sixth vertex carries a triangle, so it must be the second linear vertex
  have hwj : w = j := by
    by_contra hne
    exact no_triangle_at' hsol (cubicAt_of_two_linear hall hwi hne) hw ha hb hc (hm w hw)
      (Ne.symm hwa) (Ne.symm hwb) (Ne.symm hwc) hbc
      (by rw [show tri w a b = tri a w b from tri_ext (fun _ => by omega)]; exact Fawb)
      (by rw [show tri w a c = tri a c w from tri_ext (fun _ => by omega)]; exact Facw)
      (by rw [show tri w b c = tri b c w from tri_ext (fun _ => by omega)]; exact Fbcw)
  rw [hwj] at Fawb Facw Fbcw
  -- the L4 (triangle) link at `w = j`, whose triangle is `{a, b, c}`
  obtain ⟨p, q, r, -, -, -, -, -, -, hpq, hpr, hqr, Hj⟩ :=
    link_L4_of_linear hsol hj (hm j hj) hNj (fun y hy hyj => hnoquad j y hj hy (Ne.symm hyj))
  have ja := (Hj a b ha hb (Ne.symm hja) (Ne.symm hjb)).mp
    (by rw [show tri j a b = tri a j b from tri_ext (fun _ => by omega)]; exact Fawb)
  have jc := (Hj a c ha hc (Ne.symm hja) (Ne.symm hjc)).mp
    (by rw [show tri j a c = tri a c j from tri_ext (fun _ => by omega)]; exact Facw)
  -- closure of `A = {i, j, a, b, c}`
  have hclosed : ∀ u ∈ ({i, j, a, b, c} : Finset ℕ), ∀ x y, x < 11 → y < 11 → x ≠ u → y ≠ u →
      N (tri u x y) ≠ 0 →
      x ∈ ({i, j, a, b, c} : Finset ℕ) ∧ y ∈ ({i, j, a, b, c} : Finset ℕ) := by
    intro u hu x y hx hy hxu hyu hN
    simp only [mem_insert, mem_singleton] at hu ⊢
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · have k := (Hi x y hx hy hxu hyu).mp hN
      clear * - k; omega
    · have k := (Hj x y hx hy hxu hyu).mp hN
      have kx := mem_of_triangle_eq hab hac hbc ja.2.1 ja.2.2 jc.2.2 k.2.1
      have ky := mem_of_triangle_eq hab hac hbc ja.2.1 ja.2.2 jc.2.2 k.2.2
      clear * - kx ky; omega
    · have k := edge_mem ((Ha x y hx hy hxu hyu).mp hN)
      clear * - k hwj; omega
    · have k := edge_mem ((Hb x y hx hy hxu hyu).mp hN)
      clear * - k hwj; omega
    · have k := edge_mem ((Hc x y hx hy hxu hyu).mp hN)
      clear * - k hwj; omega
  have hlow : ∀ S, S < 2 ^ 11 → N S ≠ 0 → card 11 S ≠ 3 →
      ∀ k, S.testBit k = true → k ∈ ({i, j, a, b, c} : Finset ℕ) := by
    intro S hS hN h3 k hk
    simp only [mem_insert, mem_singleton]
    rcases hall S hS hN with rfl | rfl | h
    · left
      by_contra hne
      rw [Nat.testBit_two_pow_of_ne (Ne.symm hne)] at hk
      exact Bool.false_ne_true hk
    · right; left
      by_contra hne
      rw [Nat.testBit_two_pow_of_ne (Ne.symm hne)] at hk
      exact Bool.false_ne_true hk
    · exact absurd h h3
  have hcross := closure_local hlow hclosed
  -- five closed vertices out of eleven
  have hA5 : ({i, j, a, b, c} : Finset ℕ).card = 5 := by
    rw [card_insert_of_notMem (by
        simp only [mem_insert, mem_singleton]
        clear * - hij hai hbi hci
        omega),
      card_insert_of_notMem (by
        simp only [mem_insert, mem_singleton]
        clear * - hja hjb hjc
        omega),
      card_insert_of_notMem (by
        simp only [mem_insert, mem_singleton]
        clear * - hab hac
        omega),
      card_pair hbc]
  have hAsub : ({i, j, a, b, c} : Finset ℕ) ⊆ range 11 := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_range]
    clear * - hx hi hj ha hb hc
    omega
  have hss : ({i, j, a, b, c} : Finset ℕ) ⊂ range 11 := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hAsub, ?_⟩
    intro h
    rw [h, card_range] at hA5
    omega
  obtain ⟨u, hur, huA⟩ := Finset.exists_of_ssubset hss
  obtain ⟨T0, hT0lt, hT0bit, hT0N⟩ := hsol.2.2.2 u (mem_range.mp hur)
  have hT0A : ∀ k, T0.testBit k = true → k ∉ ({i, j, a, b, c} : Finset ℕ) := by
    rcases hcross T0 hT0lt hT0N with h | h
    · exact absurd (h u hT0bit) huA
    · exact h
  exact no_crossing_split hsol (Nat.pow_lt_pow_right (by norm_num) hi) hNi
    Nat.testBit_two_pow_self
    (by
      intro k hk
      simp only [mem_insert, mem_singleton]
      left
      by_contra hne
      rw [Nat.testBit_two_pow_of_ne (Ne.symm hne)] at hk
      exact Bool.false_ne_true hk)
    hT0lt hT0N hT0bit hT0A hcross

end R3
