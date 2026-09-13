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

lemma card_quad_le (w x y z : ℕ) : ({w, x, y, z} : Finset ℕ).card ≤ 4 := by
  have h1 := card_insert_le w ({x, y, z} : Finset ℕ)
  have h2 := card_insert_le x ({y, z} : Finset ℕ)
  have h3 := card_insert_le y ({z} : Finset ℕ)
  have h4 : ({z} : Finset ℕ).card = 1 := card_singleton z
  omega

lemma edge_symm {p q r s x y : ℕ} : Edge p q r s x y ↔ Edge p q r s y x := by
  unfold Edge; tauto

-- the cycle p-q-r-s has the same edges as its rotation q-r-s-p ...
lemma edge_rot {p q r s u t : ℕ} : Edge p q r s u t ↔ Edge q r s p u t := by
  unfold Edge; tauto

-- ... and as its reversal s-r-q-p
lemma edge_rev {p q r s u t : ℕ} : Edge p q r s u t ↔ Edge s r q p u t := by
  unfold Edge; tauto

lemma edge_mem {p q r s y z : ℕ} (h : Edge p q r s y z) :
    (y = p ∨ y = q ∨ y = r ∨ y = s) ∧ (z = p ∨ z = q ∨ z = r ∨ z = s) := by
  unfold Edge at h; constructor <;> tauto

-- the two neighbours of `y` on the cycle `p-q-r-s`, by cases on which vertex `y` is
lemma edge_nbr {p q r s x y : ℕ}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (h : Edge p q r s y x) :
    (y = p ∧ (x = q ∨ x = s)) ∨ (y = q ∧ (x = p ∨ x = r)) ∨
    (y = r ∧ (x = q ∨ x = s)) ∨ (y = s ∧ (x = r ∨ x = p)) := by
  unfold Edge at h
  clear * - hpq hpr hps hqr hqs hrs h
  omega

-- a 4-cycle has no triangle
lemma edge_no_triangle {p q r s x y z : ℕ}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hxz : x ≠ z)
    (h1 : Edge p q r s y x) (h2 : Edge p q r s y z) (h3 : Edge p q r s x z) : False := by
  have k1 := edge_nbr hpq hpr hps hqr hqs hrs h1
  have k2 := edge_nbr hpq hpr hps hqr hqs hrs h2
  have k3 := edge_nbr hpq hpr hps hqr hqs hrs h3
  clear * - hpq hpr hps hqr hqs hrs hxz k1 k2 k3
  omega

-- if `y` has the two neighbours `x` and `z` on the cycle `p-q-r-s`, the cycle is `x-y-z-w`
lemma edge_through {p q r s x y z : ℕ}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (h1 : Edge p q r s y x) (h2 : Edge p q r s y z) (hxz : x ≠ z) :
    ∃ w, w ≠ y ∧ w ≠ x ∧ w ≠ z ∧ (w = p ∨ w = q ∨ w = r ∨ w = s) ∧
      ∀ u t, Edge p q r s u t ↔ Edge x y z w u t := by
  have k1 := edge_nbr hpq hpr hps hqr hqs hrs h1
  have k2 := edge_nbr hpq hpr hps hqr hqs hrs h2
  clear * - hpq hpr hps hqr hqs hrs hxz k1 k2
  rcases k1 with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩
  · have hz : z = q ∨ z = s := by omega
    rcases hx with rfl | rfl
    · rcases hz with rfl | rfl
      · exact absurd rfl hxz
      · exact ⟨r, by omega, by omega, by omega, by omega,
          fun _ _ => edge_rev.trans (edge_rot.trans edge_rot)⟩
    · rcases hz with rfl | rfl
      · exact ⟨r, by omega, by omega, by omega, by omega,
          fun _ _ => edge_rot.trans (edge_rot.trans edge_rot)⟩
      · exact absurd rfl hxz
  · have hz : z = p ∨ z = r := by omega
    rcases hx with rfl | rfl
    · rcases hz with rfl | rfl
      · exact absurd rfl hxz
      · exact ⟨s, by omega, by omega, by omega, by omega, fun _ _ => Iff.rfl⟩
    · rcases hz with rfl | rfl
      · exact ⟨s, by omega, by omega, by omega, by omega,
          fun _ _ => edge_rev.trans edge_rot⟩
      · exact absurd rfl hxz
  · have hz : z = q ∨ z = s := by omega
    rcases hx with rfl | rfl
    · rcases hz with rfl | rfl
      · exact absurd rfl hxz
      · exact ⟨p, by omega, by omega, by omega, by omega, fun _ _ => edge_rot⟩
    · rcases hz with rfl | rfl
      · exact ⟨p, by omega, by omega, by omega, by omega, fun _ _ => edge_rev⟩
      · exact absurd rfl hxz
  · have hz : z = r ∨ z = p := by omega
    rcases hx with rfl | rfl
    · rcases hz with rfl | rfl
      · exact absurd rfl hxz
      · exact ⟨q, by omega, by omega, by omega, by omega,
          fun _ _ => edge_rot.trans edge_rot⟩
    · rcases hz with rfl | rfl
      · exact ⟨q, by omega, by omega, by omega, by omega,
          fun _ _ => edge_rev.trans (edge_rot.trans (edge_rot.trans edge_rot))⟩
      · exact absurd rfl hxz

/-! ## The link structure at a mass-4 vertex, for general `n` -/

/-- `p q r s` are four distinct vertices `< n`, all different from `v` -/
def Cyc (n v p q r s : ℕ) : Prop :=
  p < n ∧ q < n ∧ r < n ∧ s < n ∧ p ≠ v ∧ q ≠ v ∧ r ≠ v ∧ s ≠ v ∧
  p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s

/-- the support triples at `v` are exactly `v` plus an edge of the cycle p-q-r-s-p -/
def LinkIs (n : ℕ) (N : ℕ → ℤ) (v p q r s : ℕ) : Prop :=
  ∀ x y, x < n → y < n → x ≠ v → y ≠ v → (N (tri v x y) ≠ 0 ↔ Edge p q r s x y)

/-- `Cubic n N`: every set with a nonzero coefficient has exactly three elements.  This is
the `δ = 0` hypothesis of the hand proof; for `n = 12` it is automatic
(`twelve_card_three`), and for `n = 11` it is exactly the `delta = 0` case. -/
def Cubic (n : ℕ) (N : ℕ → ℤ) : Prop := ∀ S, S < 2 ^ n → N S ≠ 0 → card n S = 3

/-- under `Cubic` every link set at a vertex is a pair -/
lemma cubic_link_card_two {n : ℕ} {N : ℕ → ℤ} (hcub : Cubic n N) {v : ℕ} (hv : v < n)
    {S : ℕ} (hS : S ∈ supp n N v) : card n (S ^^^ 2 ^ v) = 2 := by
  obtain ⟨hlt, hb, hN⟩ := mem_supp.mp hS
  have h3 := hcub S hlt hN
  have h := card_xor_two_pow hv hb
  omega

/-- general `n`: the link of a mass-4 vertex of a cubic solution is a 4-cycle. -/
theorem link_cycle {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hcub : Cubic n N) {v : ℕ}
    (hv : v < n) (h4 : mass n N v = 4) :
    ∃ p q r s, p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
      ∀ S ∈ supp n N v, OnCycle p q r s (S ^^^ 2 ^ v) := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs, hall, hxor, -⟩ :=
    mass_four_link hsol hv h4
  have hmem : ∀ S ∈ ({a, b, c, d} : Finset ℕ), S ∈ supp n N v := by
    intro S hS; rw [hs]; exact hS
  have hcard2 : ∀ S ∈ ({a, b, c, d} : Finset ℕ), card n (S ^^^ 2 ^ v) = 2 :=
    fun S hS => cubic_link_card_two hcub hv (hmem S hS)
  have lt2 : ∀ S ∈ ({a, b, c, d} : Finset ℕ), S ^^^ 2 ^ v < 2 ^ n := by
    intro S hS
    exact Nat.xor_lt_two_pow (hall S hS).1 (Nat.pow_lt_pow_right (by norm_num) hv)
  obtain ⟨a1, b1, -, -, h1, e1⟩ :=
    exists_pair_of_card_two (lt2 a (by simp)) (hcard2 a (by simp))
  obtain ⟨a2, b2, -, -, h2, e2⟩ :=
    exists_pair_of_card_two (lt2 b (by simp)) (hcard2 b (by simp))
  obtain ⟨a3, b3, -, -, h3, e3⟩ :=
    exists_pair_of_card_two (lt2 c (by simp)) (hcard2 c (by simp))
  obtain ⟨a4, b4, -, -, h4', e4⟩ :=
    exists_pair_of_card_two (lt2 d (by simp)) (hcard2 d (by simp))
  have inj : ∀ x y : ℕ, x ^^^ 2 ^ v = y ^^^ 2 ^ v → x = y := by
    intro x y h
    have := congrArg (fun z => z ^^^ 2 ^ v) h
    simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this
  rw [e1, e2, e3, e4] at hxor
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, c1, c2, c3, c4⟩ :=
    four_pairs_cycle h1 h2 h3 h4'
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

/-- **General `n`.**  At a mass-4 vertex `v` of a cubic solution the support is `v` plus the
edges of a 4-cycle on four vertices `p q r s` distinct from `v`. -/
theorem link_struct {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hcub : Cubic n N) {v : ℕ}
    (hv : v < n) (h4 : mass n N v = 4) :
    ∃ p q r s, Cyc n v p q r s ∧ LinkIs n N v p q r s := by
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, hcyc⟩ := link_cycle hsol hcub hv h4
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs, -, -, -⟩ := mass_four_link hsol hv h4
  have h2v : 2 ^ v < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hv
  -- every edge of the cycle is attained by a support set
  have hex : ∀ E, OnCycle p q r s E → ∃ S ∈ supp n N v, S ^^^ 2 ^ v = E := by
    intro E hE
    have hinj : Function.Injective (fun S : ℕ => S ^^^ 2 ^ v) := by
      intro x y h
      have := congrArg (fun z => z ^^^ 2 ^ v) h
      simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using this
    have hsub : (supp n N v).image (fun S => S ^^^ 2 ^ v) ⊆
        {pair p q, pair q r, pair r s, pair s p} := by
      intro E hE
      rw [mem_image] at hE
      obtain ⟨S, hS, rfl⟩ := hE
      have := hcyc S hS
      unfold OnCycle at this
      simp only [mem_insert, mem_singleton]; exact this
    have himg : ((supp n N v).image (fun S => S ^^^ 2 ^ v)).card = 4 := by
      rw [card_image_of_injective _ hinj, hs, card_insert_of_notMem (by simp [hab, hac, had]),
        card_insert_of_notMem (by simp [hbc, hbd]), card_pair hcd]
    have hcard : ({pair p q, pair q r, pair r s, pair s p} : Finset ℕ).card ≤
        ((supp n N v).image (fun S => S ^^^ 2 ^ v)).card := by
      rw [himg]; exact card_quad_le _ _ _ _
    have heq := eq_of_subset_of_card_le hsub hcard
    have hEm : E ∈ ({pair p q, pair q r, pair r s, pair s p} : Finset ℕ) := by
      unfold OnCycle at hE
      simp only [mem_insert, mem_singleton]; exact hE
    rw [← heq, mem_image] at hEm
    exact hEm
  -- the cycle vertices are < n and ≠ v
  have hvert : ∀ x y, OnCycle p q r s (pair x y) → x < n ∧ x ≠ v := by
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
    have hS : tri v x y ∈ supp n N v :=
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

/-- `n = 12`: every vertex is a mass-4 vertex of a cubic solution. -/
lemma twelve_cubic {N : ℕ → ℤ} (hsol : IsSol 12 N) : Cubic 12 N :=
  fun _ hS hN => twelve_card_three hsol hS hN

/-- n = 12: at every vertex the support is `v` plus the edges of a 4-cycle. -/
theorem twelve_link_struct {N : ℕ → ℤ} (hsol : IsSol 12 N) {v : ℕ} (hv : v < 12) :
    ∃ p q r s, Cyc 12 v p q r s ∧ LinkIs 12 N v p q r s :=
  link_struct hsol (twelve_cubic hsol) hv (twelve_mass_four hsol hv)

/-! ## Step 3 of R3_upper_bound.md: the closure of a vertex is six vertices

From the 4-cycle link at `v` we grow the link structure at `a, b, c, d` and at the sixth
vertex `e`, and read off that no support triple crosses out of `{v,a,b,c,d,e}`.
(These six vertices carry the octahedron of the hand proof; only the non-crossing property
is exported, which is all Step 4 needs.)

Everything here is stated for general `n` with an explicit `mass n N w = 4` hypothesis at
each vertex whose link is read; `n = 12` discharges all of them through `twelve_mass_four`.

Every step is kept as a separate small lemma: heartbeats are per declaration and `omega`
is exponential in the number of disequalities in context.
-/

/-! ### the four edges of a cycle, and the permutations of a triple, as closed terms -/

lemma edge_pq (p q r s : ℕ) : Edge p q r s p q := Or.inl ⟨rfl, rfl⟩

lemma edge_qr (p q r s : ℕ) : Edge p q r s q r := Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

lemma edge_rs (p q r s : ℕ) : Edge p q r s r s :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))

lemma edge_sp (p q r s : ℕ) : Edge p q r s s p :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))

lemma tri_swap (x y z : ℕ) : tri x y z = tri y x z := tri_ext (fun _ => by omega)

lemma tri_rotl (x y z : ℕ) : tri x y z = tri y z x := tri_ext (fun _ => by omega)

lemma tri_rotr (x y z : ℕ) : tri x y z = tri z x y := tri_ext (fun _ => by omega)

/-! ### growing the link structure -/

/-- The link at the mass-4 vertex `a` contains the path `b-v-d`, so it is the 4-cycle
`b-v-d-e` for a sixth vertex `e` distinct from `a, v, b, d`. -/
lemma link_sixth {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hcub : Cubic n N) {a v b d : ℕ}
    (ha : a < n) (hvlt : v < n) (hb : b < n) (hd : d < n) (h4a : mass n N a = 4)
    (hva : v ≠ a) (hba : b ≠ a) (hda : d ≠ a) (hbd : b ≠ d)
    (F1 : N (tri a v b) ≠ 0) (F2 : N (tri a v d) ≠ 0) :
    ∃ e, e < n ∧ e ≠ a ∧ e ≠ v ∧ e ≠ b ∧ e ≠ d ∧
      ∀ p q, p < n → q < n → p ≠ a → q ≠ a → (N (tri a p q) ≠ 0 ↔ Edge b v d e p q) := by
  obtain ⟨p1, q1, r1, s1, hC1, hL1⟩ := link_struct hsol hcub ha h4a
  obtain ⟨hp1, hq1, hr1, hs1, hp1a, hq1a, hr1a, hs1a, e12, e13, e14, e23, e24, e34⟩ := hC1
  have E1 : Edge p1 q1 r1 s1 v b := (hL1 v b hvlt hb hva hba).mp F1
  have E2 : Edge p1 q1 r1 s1 v d := (hL1 v d hvlt hd hva hda).mp F2
  obtain ⟨e, hev, heb, hed, hemem, hiff⟩ := edge_through e12 e13 e14 e23 e24 e34 E1 E2 hbd
  refine ⟨e, ?_, ?_, hev, heb, hed, ?_⟩
  · rcases hemem with rfl | rfl | rfl | rfl <;> assumption
  · rcases hemem with rfl | rfl | rfl | rfl <;> assumption
  · intro p q hp hq hpa hqa
    rw [hL1 p q hp hq hpa hqa]; exact hiff p q

/-- Three faces `{w,m,x}`, `{w,m,z}`, `{w,x,u}` at the mass-4 vertex `w` (with `u ≠ m`)
determine the link at `w` completely: it is the 4-cycle `x-m-z-u`. -/
lemma link_of_three_faces {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hcub : Cubic n N)
    {w m x z u : ℕ}
    (hw : w < n) (hm : m < n) (hx : x < n) (hz : z < n) (hu : u < n) (h4w : mass n N w = 4)
    (hmw : m ≠ w) (hxw : x ≠ w) (hzw : z ≠ w) (huw : u ≠ w)
    (hxz : x ≠ z) (hmx : m ≠ x) (hum : u ≠ m)
    (F1 : N (tri w m x) ≠ 0) (F2 : N (tri w m z) ≠ 0) (F3 : N (tri w x u) ≠ 0) :
    ∀ p q, p < n → q < n → p ≠ w → q ≠ w → (N (tri w p q) ≠ 0 ↔ Edge x m z u p q) := by
  obtain ⟨p1, q1, r1, s1, hC1, hL1⟩ := link_struct hsol hcub hw h4w
  obtain ⟨-, -, -, -, -, -, -, -, e12, e13, e14, e23, e24, e34⟩ := hC1
  have E1 : Edge p1 q1 r1 s1 m x := (hL1 m x hm hx hmw hxw).mp F1
  have E2 : Edge p1 q1 r1 s1 m z := (hL1 m z hm hz hmw hzw).mp F2
  have E3 : Edge p1 q1 r1 s1 x u := (hL1 x u hx hu hxw huw).mp F3
  obtain ⟨t, htm, htx, htz, -, hiff⟩ := edge_through e12 e13 e14 e23 e24 e34 E1 E2 hxz
  have hut : u = t := by
    have hh := (hiff x u).mp E3
    unfold Edge at hh
    clear * - hh hum hmx hxz htx
    omega
  intro p q hp hq hpw hqw
  rw [hL1 p q hp hq hpw hqw, hiff p q, hut]

/-- If the sixth vertex coincided with the opposite vertex `c` of the link cycle at `v`,
the link at the mass-4 vertex `b` would contain the triangle `a-v-c`. -/
lemma no_triangle_at {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hcub : Cubic n N) {b v a c : ℕ}
    (hb : b < n) (hvlt : v < n) (ha : a < n) (hc : c < n) (h4b : mass n N b = 4)
    (hvb : v ≠ b) (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c)
    (F1 : N (tri b v a) ≠ 0) (F2 : N (tri b v c) ≠ 0) (F3 : N (tri b a c) ≠ 0) : False := by
  obtain ⟨p, q, r, s, hC, hL⟩ := link_struct hsol hcub hb h4b
  obtain ⟨-, -, -, -, -, -, -, -, f12, f13, f14, f23, f24, f34⟩ := hC
  exact edge_no_triangle f12 f13 f14 f23 f24 f34 hac
    ((hL v a hvlt ha hvb hab).mp F1) ((hL v c hvlt hc hvb hcb).mp F2)
    ((hL a c ha hc hab hcb).mp F3)

/-- Six vertices whose six link cycles all use only those six vertices are closed: no
support triple crosses between them and the rest. -/
lemma closure_of_links {n : ℕ} {N : ℕ → ℤ} {v a b c d e : ℕ} (hcub : Cubic n N)
    (hlt : v < n ∧ a < n ∧ b < n ∧ c < n ∧ d < n ∧ e < n)
    (hne : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d ∧ v ≠ e ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧
      b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e)
    (Lv : ∀ x y, x < n → y < n → x ≠ v → y ≠ v → (N (tri v x y) ≠ 0 ↔ Edge a b c d x y))
    (La : ∀ x y, x < n → y < n → x ≠ a → y ≠ a → (N (tri a x y) ≠ 0 ↔ Edge b v d e x y))
    (Lb : ∀ x y, x < n → y < n → x ≠ b → y ≠ b → (N (tri b x y) ≠ 0 ↔ Edge a v c e x y))
    (Lc : ∀ x y, x < n → y < n → x ≠ c → y ≠ c → (N (tri c x y) ≠ 0 ↔ Edge b v d e x y))
    (Ld : ∀ x y, x < n → y < n → x ≠ d → y ≠ d → (N (tri d x y) ≠ 0 ↔ Edge a v c e x y))
    (Le : ∀ x y, x < n → y < n → x ≠ e → y ≠ e → (N (tri e x y) ≠ 0 ↔ Edge b a d c x y)) :
    ∃ A : Finset ℕ, A.card = 6 ∧ A ⊆ range n ∧ v ∈ A ∧
      ∀ S, S < 2 ^ n → N S ≠ 0 →
        (∀ j, S.testBit j = true → j ∈ A) ∨ (∀ j, S.testBit j = true → j ∉ A) := by
  obtain ⟨hv, ha, hb, hc, hd, he⟩ := hlt
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15⟩ := hne
  have hclosed : ∀ w ∈ ({v, a, b, c, d, e} : Finset ℕ), ∀ x y, x < n → y < n → x ≠ w →
      y ≠ w → N (tri w x y) ≠ 0 →
      x ∈ ({v, a, b, c, d, e} : Finset ℕ) ∧ y ∈ ({v, a, b, c, d, e} : Finset ℕ) := by
    intro w hw x y hx hy hxw hyw hNw
    simp only [mem_insert, mem_singleton] at hw ⊢
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · have hm := edge_mem ((Lv x y hx hy hxw hyw).mp hNw); clear * - hm; omega
    · have hm := edge_mem ((La x y hx hy hxw hyw).mp hNw); clear * - hm; omega
    · have hm := edge_mem ((Lb x y hx hy hxw hyw).mp hNw); clear * - hm; omega
    · have hm := edge_mem ((Lc x y hx hy hxw hyw).mp hNw); clear * - hm; omega
    · have hm := edge_mem ((Ld x y hx hy hxw hyw).mp hNw); clear * - hm; omega
    · have hm := edge_mem ((Le x y hx hy hxw hyw).mp hNw); clear * - hm; omega
  refine ⟨{v, a, b, c, d, e}, ?_, ?_, by simp, ?_⟩
  · rw [card_insert_of_notMem
        (by simp only [mem_insert, mem_singleton]; clear * - n1 n2 n3 n4 n5; omega),
      card_insert_of_notMem
        (by simp only [mem_insert, mem_singleton]; clear * - n6 n7 n8 n9; omega),
      card_insert_of_notMem
        (by simp only [mem_insert, mem_singleton]; clear * - n10 n11 n12; omega),
      card_insert_of_notMem
        (by simp only [mem_insert, mem_singleton]; clear * - n13 n14; omega),
      card_pair n15]
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_range]
    clear * - hx hv ha hb hc hd he
    omega
  · intro S hS hN
    obtain ⟨x1, x2, x3, hx1, hx2, hx3, hn12, hn13, hn23, rfl⟩ :=
      exists_tri_of_card_three hS (hcub S hS hN)
    by_cases hc1 : x1 ∈ ({v, a, b, c, d, e} : Finset ℕ)
    · left
      obtain ⟨m2, m3⟩ := hclosed x1 hc1 x2 x3 hx2 hx3 (Ne.symm hn12) (Ne.symm hn13) hN
      intro j hj
      rcases mem_tri_iff.mp hj with rfl | rfl | rfl <;> assumption
    by_cases hc2 : x2 ∈ ({v, a, b, c, d, e} : Finset ℕ)
    · left
      have hN2 : N (tri x2 x1 x3) ≠ 0 := by rw [← tri_swap x1 x2 x3]; exact hN
      obtain ⟨m1, m3⟩ := hclosed x2 hc2 x1 x3 hx1 hx3 hn12 (Ne.symm hn23) hN2
      intro j hj
      rcases mem_tri_iff.mp hj with rfl | rfl | rfl <;> assumption
    by_cases hc3 : x3 ∈ ({v, a, b, c, d, e} : Finset ℕ)
    · left
      have hN3 : N (tri x3 x1 x2) ≠ 0 := by rw [← tri_rotr x1 x2 x3]; exact hN
      obtain ⟨m1, m2⟩ := hclosed x3 hc3 x1 x2 hx1 hx2 hn13 hn23 hN3
      intro j hj
      rcases mem_tri_iff.mp hj with rfl | rfl | rfl <;> assumption
    · right
      intro j hj
      rcases mem_tri_iff.mp hj with rfl | rfl | rfl <;> assumption

/-- **Step 3 of R3_upper_bound.md (topology-free), general `n`.**  In a cubic solution all of
whose vertices have mass 4, every vertex `v` lies in a set `A` of six vertices such that no
support triple crosses between `A` and its complement.

The hypothesis `hall4` is used at the six vertices of `A` only, but those six are produced by
the proof and cannot be named in the statement; see the note in `PLAN_F11.md` on why the
conclusion genuinely needs the link of *every* vertex of `A`. -/
theorem octahedron_closure_gen {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hcub : Cubic n N)
    (hall4 : ∀ w, w < n → mass n N w = 4) {v : ℕ} (hv : v < n) :
    ∃ A : Finset ℕ, A.card = 6 ∧ A ⊆ range n ∧ v ∈ A ∧
      ∀ S, S < 2 ^ n → N S ≠ 0 →
        (∀ j, S.testBit j = true → j ∈ A) ∨ (∀ j, S.testBit j = true → j ∉ A) := by
  obtain ⟨a, b, c, d, hC, hL⟩ := link_struct hsol hcub hv (hall4 v hv)
  obtain ⟨ha12, hb12, hc12, hd12, hav, hbv, hcv, hdv, hab, hac, had, hbc, hbd, hcd⟩ := hC
  -- the four faces at v
  have Fvab : N (tri v a b) ≠ 0 := (hL a b ha12 hb12 hav hbv).mpr (edge_pq a b c d)
  have Fvbc : N (tri v b c) ≠ 0 := (hL b c hb12 hc12 hbv hcv).mpr (edge_qr a b c d)
  have Fvcd : N (tri v c d) ≠ 0 := (hL c d hc12 hd12 hcv hdv).mpr (edge_rs a b c d)
  have Fvda : N (tri v d a) ≠ 0 := (hL d a hd12 ha12 hdv hav).mpr (edge_sp a b c d)
  -- the link at a is b-v-d-e
  obtain ⟨e, he12, hea, hev, heb, hed, hLa⟩ := link_sixth hsol hcub ha12 hv hb12 hd12
    (hall4 a ha12) (Ne.symm hav) (Ne.symm hab) (Ne.symm had) hbd
    (by rw [tri_swap a v b]; exact Fvab) (by rw [tri_rotl a v d]; exact Fvda)
  have Fade : N (tri a d e) ≠ 0 := (hLa d e hd12 he12 (Ne.symm had) hea).mpr (edge_rs b v d e)
  have Faeb : N (tri a e b) ≠ 0 := (hLa e b he12 hb12 hea (Ne.symm hab)).mpr (edge_sp b v d e)
  -- the sixth vertex is not the opposite vertex c
  have hec : e ≠ c := by
    intro hEC
    have Facb : N (tri a c b) ≠ 0 := by
      refine (hLa c b hc12 hb12 (Ne.symm hac) (Ne.symm hab)).mpr ?_
      rw [← hEC]; exact edge_sp b v d e
    exact no_triangle_at hsol hcub hb12 hv ha12 hc12 (hall4 b hb12)
      (Ne.symm hbv) hab (Ne.symm hbc) hac
      (by rw [tri_rotl b v a]; exact Fvab) (by rw [tri_swap b v c]; exact Fvbc)
      (by rw [tri_rotl b a c]; exact Facb)
  -- the links at b, d, c, e
  have hLb := link_of_three_faces hsol hcub hb12 hv ha12 hc12 he12 (hall4 b hb12)
    (Ne.symm hbv) hab (Ne.symm hbc) heb hac (Ne.symm hav) hev
    (by rw [tri_rotl b v a]; exact Fvab) (by rw [tri_swap b v c]; exact Fvbc)
    (by rw [tri_rotl b a e]; exact Faeb)
  have hLd := link_of_three_faces hsol hcub hd12 hv ha12 hc12 he12 (hall4 d hd12)
    (Ne.symm hdv) had hcd hed hac (Ne.symm hav) hev
    (by rw [tri_swap d v a]; exact Fvda) (by rw [tri_rotl d v c]; exact Fvcd)
    (by rw [tri_swap d a e]; exact Fade)
  have Fbce : N (tri b c e) ≠ 0 := (hLb c e hc12 he12 (Ne.symm hbc) heb).mpr (edge_rs a v c e)
  have hLc := link_of_three_faces hsol hcub hc12 hv hb12 hd12 he12 (hall4 c hc12)
    (Ne.symm hcv) hbc (Ne.symm hcd) hec hbd (Ne.symm hbv) hev
    (by rw [tri_rotl c v b]; exact Fvbc) (by rw [tri_swap c v d]; exact Fvcd)
    (by rw [tri_swap c b e]; exact Fbce)
  have hLe := link_of_three_faces hsol hcub he12 ha12 hb12 hd12 hc12 (hall4 e he12)
    (Ne.symm hea) (Ne.symm heb) (Ne.symm hed) (Ne.symm hec) hbd hab (Ne.symm hac)
    (by rw [tri_swap e a b]; exact Faeb) (by rw [tri_rotl e a d]; exact Fade)
    (by rw [tri_rotl e b c]; exact Fbce)
  exact closure_of_links hcub ⟨hv, ha12, hb12, hc12, hd12, he12⟩
    ⟨Ne.symm hav, Ne.symm hbv, Ne.symm hcv, Ne.symm hdv, Ne.symm hev, hab, hac, had,
      Ne.symm hea, hbc, hbd, Ne.symm heb, hcd, Ne.symm hec, Ne.symm hed⟩
    hL hLa hLb hLc hLd hLe

/-- **Step 3 of R3_upper_bound.md (topology-free).**  In a 12-variable solution every vertex
`v` lies in a set `A` of six vertices such that no support triple crosses between `A` and its
complement. -/
theorem octahedron_closure {N : ℕ → ℤ} (hsol : IsSol 12 N) {v : ℕ} (hv : v < 12) :
    ∃ A : Finset ℕ, A.card = 6 ∧ A ⊆ range 12 ∧ v ∈ A ∧
      ∀ S, S < 2 ^ 12 → N S ≠ 0 →
        (∀ j, S.testBit j = true → j ∈ A) ∨ (∀ j, S.testBit j = true → j ∉ A) :=
  octahedron_closure_gen hsol (twelve_cubic hsol) (fun w hw => twelve_mass_four hsol hw) hv

end R3
