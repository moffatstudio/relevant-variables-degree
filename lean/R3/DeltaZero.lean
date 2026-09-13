import R3.Final
import R3.LinkTypes
/-!
# Case `δ = 0` of R3_equals_10.md at `n = 11`

`δ = 0` is the case in which every support set is a triple (`Cubic 11 N`).  Then
`∑_v mass v = 3 * 16 = 48` while every mass is at least 4, so the eleven masses are
`(8, 4^10)` or `(6, 6, 4^9)`: **at most two vertices are exceptional**
(`card_mass_ne_four_le_two`).

`octahedron_closure_gen` needs *every* vertex to have mass 4, which never happens here.
This file localises it: the closure at `v` only ever reads the links of `v`, of the four
vertices of its link cycle, and of the sixth vertex — all of which lie within distance two
of `v` in the support hypergraph (`Near`).  So

* `closure_near` : if every vertex `Near` to `v` has mass 4, the six-set of `v` is closed;
* `closure_kills` : with `6 < n` that is already a contradiction (`no_crossing_split`).

Hence in the residual `δ = 0` situation **every** mass-4 vertex has an exceptional vertex
within distance two (`delta_zero_residual`).
-/
namespace R3
open Finset

/-! ## Distance in the support hypergraph -/

/-- `v` and `w` lie together in some support set. -/
def Nbr (n : ℕ) (N : ℕ → ℤ) (v w : ℕ) : Prop :=
  ∃ S, S < 2 ^ n ∧ N S ≠ 0 ∧ S.testBit v = true ∧ S.testBit w = true

/-- `w` is within distance two of `v` in the support hypergraph. -/
def Near (n : ℕ) (N : ℕ → ℤ) (v w : ℕ) : Prop :=
  Nbr n N v w ∨ ∃ u, u < n ∧ Nbr n N v u ∧ Nbr n N u w

lemma nbr_tri_snd {n : ℕ} {N : ℕ → ℤ} {x y z : ℕ} (hx : x < n) (hy : y < n) (hz : z < n)
    (h : N (tri x y z) ≠ 0) : Nbr n N x y :=
  ⟨tri x y z, tri_lt hx hy hz, h, mem_tri_iff.mpr (Or.inl rfl),
    mem_tri_iff.mpr (Or.inr (Or.inl rfl))⟩

lemma nbr_tri_thd {n : ℕ} {N : ℕ → ℤ} {x y z : ℕ} (hx : x < n) (hy : y < n) (hz : z < n)
    (h : N (tri x y z) ≠ 0) : Nbr n N x z :=
  ⟨tri x y z, tri_lt hx hy hz, h, mem_tri_iff.mpr (Or.inl rfl),
    mem_tri_iff.mpr (Or.inr (Or.inr rfl))⟩

lemma near_self {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) {v : ℕ} (hv : v < n) :
    Near n N v v := by
  obtain ⟨S, hS⟩ := supp_nonempty hsol hv
  obtain ⟨hlt, hb, hN⟩ := mem_supp.mp hS
  exact Or.inl ⟨S, hlt, hN, hb, hb⟩

/-! ## The localised octahedron closure -/

/-- **Localised `octahedron_closure_gen`.**  The proof of `octahedron_closure_gen` uses the
mass-4 hypothesis only at `v`, at the four vertices `a b c d` of its link cycle and at the
sixth vertex `e`.  Each of those lies within distance two of `v`, so the global hypothesis
`∀ w < n, mass n N w = 4` can be replaced by `∀ w < n, Near n N v w → mass n N w = 4`. -/
theorem closure_near {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hcub : Cubic n N) {v : ℕ}
    (hv : v < n) (hnear : ∀ w, w < n → Near n N v w → mass n N w = 4) :
    ∃ A : Finset ℕ, A.card = 6 ∧ A ⊆ range n ∧ v ∈ A ∧
      ∀ S, S < 2 ^ n → N S ≠ 0 →
        (∀ j, S.testBit j = true → j ∈ A) ∨ (∀ j, S.testBit j = true → j ∉ A) := by
  have m4v : mass n N v = 4 := hnear v hv (near_self hsol hv)
  obtain ⟨a, b, c, d, hC, hL⟩ := link_struct hsol hcub hv m4v
  obtain ⟨ha12, hb12, hc12, hd12, hav, hbv, hcv, hdv, hab, hac, had, hbc, hbd, hcd⟩ := hC
  -- the four faces at v
  have Fvab : N (tri v a b) ≠ 0 := (hL a b ha12 hb12 hav hbv).mpr (edge_pq a b c d)
  have Fvbc : N (tri v b c) ≠ 0 := (hL b c hb12 hc12 hbv hcv).mpr (edge_qr a b c d)
  have Fvcd : N (tri v c d) ≠ 0 := (hL c d hc12 hd12 hcv hdv).mpr (edge_rs a b c d)
  have Fvda : N (tri v d a) ≠ 0 := (hL d a hd12 ha12 hdv hav).mpr (edge_sp a b c d)
  -- the four link vertices are neighbours of `v`
  have nva : Nbr n N v a := nbr_tri_snd hv ha12 hb12 Fvab
  have nvb : Nbr n N v b := nbr_tri_thd hv ha12 hb12 Fvab
  have nvc : Nbr n N v c := nbr_tri_thd hv hb12 hc12 Fvbc
  have nvd : Nbr n N v d := nbr_tri_thd hv hc12 hd12 Fvcd
  have m4a : mass n N a = 4 := hnear a ha12 (Or.inl nva)
  have m4b : mass n N b = 4 := hnear b hb12 (Or.inl nvb)
  have m4c : mass n N c = 4 := hnear c hc12 (Or.inl nvc)
  have m4d : mass n N d = 4 := hnear d hd12 (Or.inl nvd)
  -- the link at a is b-v-d-e
  obtain ⟨e, he12, hea, hev, heb, hed, hLa⟩ := link_sixth hsol hcub ha12 hv hb12 hd12
    m4a (Ne.symm hav) (Ne.symm hab) (Ne.symm had) hbd
    (by rw [tri_swap a v b]; exact Fvab) (by rw [tri_rotl a v d]; exact Fvda)
  have Fade : N (tri a d e) ≠ 0 := (hLa d e hd12 he12 (Ne.symm had) hea).mpr (edge_rs b v d e)
  have Faeb : N (tri a e b) ≠ 0 := (hLa e b he12 hb12 hea (Ne.symm hab)).mpr (edge_sp b v d e)
  -- the sixth vertex is within distance two of `v`
  have m4e : mass n N e = 4 :=
    hnear e he12 (Or.inr ⟨a, ha12, nva, nbr_tri_thd ha12 hd12 he12 Fade⟩)
  -- the sixth vertex is not the opposite vertex c
  have hec : e ≠ c := by
    intro hEC
    have Facb : N (tri a c b) ≠ 0 := by
      refine (hLa c b hc12 hb12 (Ne.symm hac) (Ne.symm hab)).mpr ?_
      rw [← hEC]; exact edge_sp b v d e
    exact no_triangle_at hsol hcub hb12 hv ha12 hc12 m4b
      (Ne.symm hbv) hab (Ne.symm hbc) hac
      (by rw [tri_rotl b v a]; exact Fvab) (by rw [tri_swap b v c]; exact Fvbc)
      (by rw [tri_rotl b a c]; exact Facb)
  -- the links at b, d, c, e
  have hLb := link_of_three_faces hsol hcub hb12 hv ha12 hc12 he12 m4b
    (Ne.symm hbv) hab (Ne.symm hbc) heb hac (Ne.symm hav) hev
    (by rw [tri_rotl b v a]; exact Fvab) (by rw [tri_swap b v c]; exact Fvbc)
    (by rw [tri_rotl b a e]; exact Faeb)
  have hLd := link_of_three_faces hsol hcub hd12 hv ha12 hc12 he12 m4d
    (Ne.symm hdv) had hcd hed hac (Ne.symm hav) hev
    (by rw [tri_swap d v a]; exact Fvda) (by rw [tri_rotl d v c]; exact Fvcd)
    (by rw [tri_swap d a e]; exact Fade)
  have Fbce : N (tri b c e) ≠ 0 := (hLb c e hc12 he12 (Ne.symm hbc) heb).mpr (edge_rs a v c e)
  have hLc := link_of_three_faces hsol hcub hc12 hv hb12 hd12 he12 m4c
    (Ne.symm hcv) hbc (Ne.symm hcd) hec hbd (Ne.symm hbv) hev
    (by rw [tri_rotl c v b]; exact Fvbc) (by rw [tri_swap c v d]; exact Fvcd)
    (by rw [tri_swap c b e]; exact Fbce)
  have hLe := link_of_three_faces hsol hcub he12 ha12 hb12 hd12 hc12 m4e
    (Ne.symm hea) (Ne.symm heb) (Ne.symm hed) (Ne.symm hec) hbd hab (Ne.symm hac)
    (by rw [tri_swap e a b]; exact Faeb) (by rw [tri_rotl e a d]; exact Fade)
    (by rw [tri_rotl e b c]; exact Fbce)
  exact closure_of_links hcub ⟨hv, ha12, hb12, hc12, hd12, he12⟩
    ⟨Ne.symm hav, Ne.symm hbv, Ne.symm hcv, Ne.symm hdv, Ne.symm hev, hab, hac, had,
      Ne.symm hea, hbc, hbd, Ne.symm heb, hcd, Ne.symm hec, Ne.symm hed⟩
    hL hLa hLb hLc hLd hLe

/-- **Step (a) of the `δ = 0` plan.**  If every vertex within distance two of `v` has mass
4 and there are more than six vertices, the solution does not exist. -/
theorem closure_kills {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hcub : Cubic n N)
    (hn : 6 < n) {v : ℕ} (hv : v < n)
    (hnear : ∀ w, w < n → Near n N v w → mass n N w = 4) : False := by
  obtain ⟨A, hcard, hAsub, hvA, hcross⟩ := closure_near hsol hcub hv hnear
  obtain ⟨S0, hS0lt, hS0bit, hS0N⟩ := hsol.2.2.2 v hv
  have hS0A : ∀ j, S0.testBit j = true → j ∈ A := by
    rcases hcross S0 hS0lt hS0N with h | h
    · exact h
    · exact absurd hvA (h v hS0bit)
  have hss : A ⊂ range n := by
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

/-- **The residual `δ = 0` situation.**  In a cubic solution on `n > 6` variables every
vertex has an exceptional vertex (mass ≠ 4) within distance two.  At `n = 11` there are at
most two exceptional vertices (`card_mass_ne_four_le_two`), so the whole support is squeezed
into a neighbourhood of them; that is the finite family the remaining work must kill. -/
theorem delta_zero_residual {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hcub : Cubic n N)
    (hn : 6 < n) {v : ℕ} (hv : v < n) :
    ∃ w, w < n ∧ Near n N v w ∧ mass n N w ≠ 4 := by
  by_contra hcon
  push_neg at hcon
  exact closure_kills hsol hcub hn hv (fun w hw hnw => hcon w hw hnw)

/-! ## The pseudo-manifold property: a pair through a mass-4 vertex lies in 0 or 2 triples -/

/-- On a 4-cycle every vertex that has one neighbour has a second, different one. -/
lemma edge_second {p q r s v y : ℕ}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (h : Edge p q r s v y) :
    ∃ z, z ≠ y ∧ (z = p ∨ z = q ∨ z = r ∨ z = s) ∧ Edge p q r s v z := by
  rcases edge_nbr hpq hpr hps hqr hqs hrs h with
    ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩
  · rcases hx with rfl | rfl
    · exact ⟨s, by omega, by omega, edge_symm.mp (edge_sp _ _ _ _)⟩
    · exact ⟨q, by omega, by omega, edge_pq _ _ _ _⟩
  · rcases hx with rfl | rfl
    · exact ⟨r, by omega, by omega, edge_qr _ _ _ _⟩
    · exact ⟨p, by omega, by omega, edge_symm.mp (edge_pq _ _ _ _)⟩
  · rcases hx with rfl | rfl
    · exact ⟨s, by omega, by omega, edge_rs _ _ _ _⟩
    · exact ⟨q, by omega, by omega, edge_symm.mp (edge_qr _ _ _ _)⟩
  · rcases hx with rfl | rfl
    · exact ⟨p, by omega, by omega, edge_sp _ _ _ _⟩
    · exact ⟨r, by omega, by omega, edge_symm.mp (edge_rs _ _ _ _)⟩

/-- On a 4-cycle no vertex has three distinct neighbours. -/
lemma edge_not_three {p q r s v y z w : ℕ}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (h1 : Edge p q r s v y) (h2 : Edge p q r s v z) (h3 : Edge p q r s v w) : False := by
  have k1 := edge_nbr hpq hpr hps hqr hqs hrs h1
  have k2 := edge_nbr hpq hpr hps hqr hqs hrs h2
  have k3 := edge_nbr hpq hpr hps hqr hqs hrs h3
  clear * - hpq hpr hps hqr hqs hrs hyz hyw hzw k1 k2 k3
  omega

/-- **Second triple through a pair.**  In a cubic solution, if `x` has mass 4 and the triple
`{x, v, y}` is in the support, then there is a second support triple `{x, v, z}` through the
pair `{x, v}`, with `z ≠ y`.  (The link of `x` is a 4-cycle, in which `v` has degree 2.) -/
theorem pair_second {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hcub : Cubic n N)
    {x v y : ℕ} (hx : x < n) (hv : v < n) (hy : y < n) (h4 : mass n N x = 4)
    (hvx : v ≠ x) (hyx : y ≠ x) (hF : N (tri x v y) ≠ 0) :
    ∃ z, z < n ∧ z ≠ x ∧ z ≠ y ∧ N (tri x v z) ≠ 0 := by
  obtain ⟨p, q, r, s, hC, hL⟩ := link_struct hsol hcub hx h4
  obtain ⟨hp, hq, hr, hs, hpx, hqx, hrx, hsx, hpq, hpr, hps, hqr, hqs, hrs⟩ := hC
  have E : Edge p q r s v y := (hL v y hv hy hvx hyx).mp hF
  obtain ⟨z, hzy, hzmem, hz⟩ := edge_second hpq hpr hps hqr hqs hrs E
  refine ⟨z, ?_, ?_, hzy, ?_⟩
  · rcases hzmem with rfl | rfl | rfl | rfl <;> assumption
  · rcases hzmem with rfl | rfl | rfl | rfl <;> assumption
  · refine (hL v z hv ?_ hvx ?_).mpr hz
    · rcases hzmem with rfl | rfl | rfl | rfl <;> assumption
    · rcases hzmem with rfl | rfl | rfl | rfl <;> assumption

/-- **No pair lies in three triples.**  In a cubic solution a pair `{x, v}` with
`mass x = 4` lies in at most two support triples: `λ_{xv} ≤ 2`.  This is the Lean form of
"`v` has degree at most 2 in the link of `x`", the first step of the `(8, 4^10)` sub-case. -/
theorem pair_not_three {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hcub : Cubic n N)
    {x v y z w : ℕ} (hx : x < n) (hv : v < n) (hy : y < n) (hz : z < n) (hw : w < n)
    (h4 : mass n N x = 4) (hvx : v ≠ x) (hyx : y ≠ x) (hzx : z ≠ x) (hwx : w ≠ x)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (F1 : N (tri x v y) ≠ 0) (F2 : N (tri x v z) ≠ 0) (F3 : N (tri x v w) ≠ 0) : False := by
  obtain ⟨p, q, r, s, hC, hL⟩ := link_struct hsol hcub hx h4
  obtain ⟨-, -, -, -, -, -, -, -, hpq, hpr, hps, hqr, hqs, hrs⟩ := hC
  exact edge_not_three hpq hpr hps hqr hqs hrs hyz hyw hzw
    ((hL v y hv hy hvx hyx).mp F1) ((hL v z hv hz hvx hzx).mp F2)
    ((hL v w hv hw hvx hwx).mp F3)

/-- `n = 11` corollary: in a homogeneous cubic (`δ = 0`) solution on eleven variables every
vertex has an exceptional vertex within distance two.  Since at most two vertices are
exceptional (`card_mass_ne_four_le_two`), the entire support is squeezed into the distance-2
neighbourhood of those one or two vertices. -/
theorem eleven_delta_zero_residual {N : ℕ → ℤ} (hsol : IsSol 11 N) (hcub : Cubic 11 N)
    {v : ℕ} (hv : v < 11) : ∃ w, w < 11 ∧ Near 11 N v w ∧ mass 11 N w ≠ 4 :=
  delta_zero_residual hsol hcub (by norm_num) hv

/-! ## Mass counting: a mass-4 vertex is exhausted by four support triples -/

lemma ne_of_testBit {A B j : ℕ} (h1 : A.testBit j = true) (h2 : B.testBit j = false) :
    A ≠ B := by
  intro h; rw [h, h2] at h1; simp at h1

lemma tri_testBit_false {a b c j : ℕ} (ha : j ≠ a) (hb : j ≠ b) (hc : j ≠ c) :
    (tri a b c).testBit j = false := by
  cases hj : (tri a b c).testBit j with
  | false => rfl
  | true => rcases mem_tri_iff.mp hj with rfl | rfl | rfl <;> simp at ha hb hc

lemma tri_mem_supp {n : ℕ} {N : ℕ → ℤ} {x y z : ℕ} (hx : x < n) (hy : y < n)
    (hz : z < n) (h : N (tri x y z) ≠ 0) : tri x y z ∈ supp n N x :=
  mem_supp.mpr ⟨tri_lt hx hy hz, mem_tri_iff.mpr (Or.inl rfl), h⟩

/-- the number of support sets at `v` is at most its mass -/
lemma card_supp_le_mass {n : ℕ} {N : ℕ → ℤ} (v : ℕ) :
    ((supp n N v).card : ℤ) ≤ mass n N v := by
  have h1 : ∀ S ∈ supp n N v, (1 : ℤ) ≤ N S ^ 2 :=
    fun S hS => one_le_sq_of_ne_zero (mem_supp.mp hS).2.2
  calc ((supp n N v).card : ℤ) = ∑ _S ∈ supp n N v, (1 : ℤ) := by simp
    _ ≤ ∑ S ∈ supp n N v, N S ^ 2 := Finset.sum_le_sum h1
    _ = mass n N v := (mass_eq_sum_supp n N v).symm

lemma card_quad_eq {w x y z : ℕ} (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ({w, x, y, z} : Finset ℕ).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hwx, hwy, hwz]),
    Finset.card_insert_of_notMem (by simp [hxy, hxz]),
    Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]

/-- **Exhaustion.**  Four distinct support sets at a mass-4 vertex are all of them. -/
theorem supp_eq_quad {n : ℕ} {N : ℕ → ℤ} {v S1 S2 S3 S4 : ℕ} (h4 : mass n N v = 4)
    (h1 : S1 ∈ supp n N v) (h2 : S2 ∈ supp n N v) (h3 : S3 ∈ supp n N v)
    (h4' : S4 ∈ supp n N v)
    (n12 : S1 ≠ S2) (n13 : S1 ≠ S3) (n14 : S1 ≠ S4) (n23 : S2 ≠ S3) (n24 : S2 ≠ S4)
    (n34 : S3 ≠ S4) : supp n N v = {S1, S2, S3, S4} := by
  have hsub : ({S1, S2, S3, S4} : Finset ℕ) ⊆ supp n N v := by
    intro T hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl <;> assumption
  have hcard : (supp n N v).card ≤ ({S1, S2, S3, S4} : Finset ℕ).card := by
    rw [card_quad_eq n12 n13 n14 n23 n24 n34]
    have h := card_supp_le_mass (n := n) (N := N) v
    rw [h4] at h
    exact_mod_cast h
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- A fifth support set at a mass-4 vertex is impossible. -/
theorem no_fifth_supp {n : ℕ} {N : ℕ → ℤ} {v S1 S2 S3 S4 T : ℕ} (h4 : mass n N v = 4)
    (h1 : S1 ∈ supp n N v) (h2 : S2 ∈ supp n N v) (h3 : S3 ∈ supp n N v)
    (h4' : S4 ∈ supp n N v) (hT : T ∈ supp n N v)
    (n12 : S1 ≠ S2) (n13 : S1 ≠ S3) (n14 : S1 ≠ S4) (n23 : S2 ≠ S3) (n24 : S2 ≠ S4)
    (n34 : S3 ≠ S4) : T = S1 ∨ T = S2 ∨ T = S3 ∨ T = S4 := by
  have hq := supp_eq_quad h4 h1 h2 h3 h4' n12 n13 n14 n23 n24 n34
  rw [hq] at hT
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hT

/-! ## Triples: permutations, distinctness, and the second triple through `{v, x}` -/

lemma tri_swap23 (x y z : ℕ) : tri x y z = tri x z y := tri_ext (fun _ => by omega)

lemma card_pair_le (x z : ℕ) : ({x, z} : Finset ℕ).card ≤ 2 := by
  simpa using Finset.card_insert_le x ({z} : Finset ℕ)

lemma card_tri_le (n x y z : ℕ) : card n (tri x y z) ≤ ({x, y, z} : Finset ℕ).card := by
  unfold card
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi
  rcases mem_tri_iff.mp hi.2 with rfl | rfl | rfl <;> simp

/-- in a cubic solution the three vertices of a support triple are distinct -/
lemma tri_distinct {n : ℕ} {N : ℕ → ℤ} (hcub : Cubic n N) {x y z : ℕ}
    (hx : x < n) (hy : y < n) (hz : z < n) (h : N (tri x y z) ≠ 0) :
    x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  have h3 := hcub _ (tri_lt hx hy hz) h
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · have hc := card_tri_le n x x z
    have : ({x, x, z} : Finset ℕ).card ≤ 2 := by
      simpa using card_pair_le x z
    omega
  · have hc := card_tri_le n x y x
    have : ({x, y, x} : Finset ℕ).card ≤ 2 := by
      have : ({x, y, x} : Finset ℕ) = {x, y} := by
        ext j; simp; tauto
      rw [this]; exact card_pair_le x y
    omega
  · have hc := card_tri_le n x y y
    have : ({x, y, y} : Finset ℕ).card ≤ 2 := by
      simpa using card_pair_le x y
    omega

/-- **The second triple through a pair, with full distinctness.**  If `mass a = 4` and
`{v, a, b}` is a support triple of a cubic solution, there is a second support triple
`{v, a, b'}` with `b'` different from `a`, `b` and `v`. -/
theorem second_v_triple {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hcub : Cubic n N)
    {v a b : ℕ} (hv : v < n) (ha : a < n) (hb : b < n) (h4 : mass n N a = 4)
    (hva : v ≠ a) (hba : b ≠ a) (hF : N (tri a v b) ≠ 0) :
    ∃ b', b' < n ∧ b' ≠ a ∧ b' ≠ b ∧ b' ≠ v ∧ N (tri a v b') ≠ 0 := by
  obtain ⟨b', hb'lt, hb'a, hb'b, hF'⟩ := pair_second hsol hcub ha hv hb h4 hva hba hF
  refine ⟨b', hb'lt, hb'a, hb'b, ?_, hF'⟩
  have hd := tri_distinct hcub ha hv hb'lt hF'
  exact fun h => hd.2.2 h.symm

/-! ## Lemma Y, local form: two mass-4 ends of a support triple share an apex -/

/-- **Lemma Y (local step).**  Let `{v, a, b}` be a support triple of a cubic solution with
`mass a = mass b = 4`.  Then the links of `a` and of `b` are the 4-cycles `b-v-b'-y` and
`a-v-a'-y` with the *same* apex `y`: the pair `{a, b}` lies in exactly the two triples
`{v,a,b}` and `{y,a,b}`, which is what forces `y` to be shared. -/
theorem octa_half {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hcub : Cubic n N)
    {v a b : ℕ} (hv : v < n) (ha : a < n) (hb : b < n)
    (h4a : mass n N a = 4) (h4b : mass n N b = 4)
    (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b) (hF : N (tri a v b) ≠ 0) :
    ∃ a' b' y, a' < n ∧ b' < n ∧ y < n ∧
      a' ≠ a ∧ a' ≠ b ∧ a' ≠ v ∧ a' ≠ y ∧ b' ≠ a ∧ b' ≠ b ∧ b' ≠ v ∧ b' ≠ y ∧
      y ≠ a ∧ y ≠ b ∧ y ≠ v ∧
      (∀ p q, p < n → q < n → p ≠ a → q ≠ a → (N (tri a p q) ≠ 0 ↔ Edge b v b' y p q)) ∧
      (∀ p q, p < n → q < n → p ≠ b → q ≠ b → (N (tri b p q) ≠ 0 ↔ Edge a v a' y p q)) := by
  -- the second `v`-triple at `a`, and the link of `a`
  obtain ⟨b', hb'lt, hb'a, hb'b, hb'v, Fab'⟩ :=
    second_v_triple hsol hcub hv ha hb h4a (Ne.symm hav) (Ne.symm hab) hF
  obtain ⟨y1, hy1lt, hy1a, hy1v, hy1b, hy1b', hLa⟩ :=
    link_sixth hsol hcub ha hv hb hb'lt h4a (Ne.symm hav) (Ne.symm hab) hb'a
      (Ne.symm hb'b) hF Fab'
  -- the same at `b`
  have hFb : N (tri b v a) ≠ 0 := by
    have e1 : tri b v a = tri a v b := tri_ext (fun _ => by omega)
    rw [e1]; exact hF
  obtain ⟨a', ha'lt, ha'b, ha'a, ha'v, Fba'⟩ :=
    second_v_triple hsol hcub hv hb ha h4b (Ne.symm hbv) hab hFb
  obtain ⟨y2, hy2lt, hy2b, hy2v, hy2a, hy2a', hLb⟩ :=
    link_sixth hsol hcub hb hv ha ha'lt h4b (Ne.symm hbv) hab ha'b
      (Ne.symm ha'a) hFb Fba'
  -- the pair `{a, b}` lies in three triples unless the two apexes agree
  have T0 : N (tri a b v) ≠ 0 := by
    have e1 : tri a b v = tri a v b := tri_ext (fun _ => by omega)
    rw [e1]; exact hF
  have T1 : N (tri a b y1) ≠ 0 := by
    have e1 : tri a b y1 = tri a y1 b := tri_ext (fun _ => by omega)
    rw [e1]
    exact (hLa y1 b hy1lt hb hy1a (Ne.symm hab)).mpr (edge_sp b v b' y1)
  have T2 : N (tri a b y2) ≠ 0 := by
    have e1 : tri a b y2 = tri b y2 a := tri_ext (fun _ => by omega)
    rw [e1]
    exact (hLb y2 a hy2lt ha hy2b hab).mpr (edge_sp a v a' y2)
  have hy : y1 = y2 := by
    by_contra hne
    exact pair_not_three hsol hcub ha hb hv hy1lt hy2lt h4a (Ne.symm hab) (Ne.symm hav)
      hy1a hy2a (Ne.symm hy1v) (Ne.symm hy2v) hne T0 T1 T2
  subst hy
  exact ⟨a', b', y1, ha'lt, hb'lt, hy1lt, ha'a, ha'b, ha'v, Ne.symm hy2a', hb'a, hb'b,
    hb'v, Ne.symm hy1b', hy1a, hy1b, hy1v, hLa, hLb⟩

/-! ## Mass 8: there is always a fifth support set -/

/-- the square of a nonzero integer is `1`, `4`, or at least `9` -/
lemma sq_cases {x : ℤ} (h : x ≠ 0) : x ^ 2 = 1 ∨ x ^ 2 = 4 ∨ 9 ≤ x ^ 2 := by
  have hx : 1 ≤ |x| := by
    rcases lt_trichotomy x 0 with h' | h' | h'
    · rw [abs_of_neg h']; omega
    · exact absurd h' h
    · rw [abs_of_pos h']; omega
  have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  rcases lt_trichotomy |x| 2 with h2 | h2 | h2
  · have h1 : |x| = 1 := by omega
    left; rw [hsq, h1]; norm_num
  · right; left; rw [hsq, h2]; norm_num
  · right; right; rw [hsq]; nlinarith

/-- four values, each `1`, `4` or at least `9`, never sum to `8` -/
lemma four_vals_ne_eight {A B C D : ℤ} (hA : A = 1 ∨ A = 4 ∨ 9 ≤ A)
    (hB : B = 1 ∨ B = 4 ∨ 9 ≤ B) (hC : C = 1 ∨ C = 4 ∨ 9 ≤ C)
    (hD : D = 1 ∨ D = 4 ∨ 9 ≤ D) : A + (B + (C + D)) ≠ 8 := by omega

/-- **A mass-8 vertex has at least five support sets.**  Four nonzero squares never sum
to `8`, so four distinct support sets at a vertex of mass 8 are never all of them. -/
theorem exists_fifth_supp {n : ℕ} {N : ℕ → ℤ} {v S1 S2 S3 S4 : ℕ} (h8 : mass n N v = 8)
    (h1 : S1 ∈ supp n N v) (h2 : S2 ∈ supp n N v) (h3 : S3 ∈ supp n N v)
    (h4 : S4 ∈ supp n N v)
    (n12 : S1 ≠ S2) (n13 : S1 ≠ S3) (n14 : S1 ≠ S4) (n23 : S2 ≠ S3) (n24 : S2 ≠ S4)
    (n34 : S3 ≠ S4) :
    ∃ T, T ∈ supp n N v ∧ T ≠ S1 ∧ T ≠ S2 ∧ T ≠ S3 ∧ T ≠ S4 := by
  by_contra hcon
  push_neg at hcon
  have hsub : supp n N v ⊆ ({S1, S2, S3, S4} : Finset ℕ) := by
    intro T hT
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases e1 : T = S1
    · exact Or.inl e1
    by_cases e2 : T = S2
    · exact Or.inr (Or.inl e2)
    by_cases e3 : T = S3
    · exact Or.inr (Or.inr (Or.inl e3))
    exact Or.inr (Or.inr (Or.inr (hcon T hT e1 e2 e3)))
  have hsup : ({S1, S2, S3, S4} : Finset ℕ) ⊆ supp n N v := by
    intro T hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl <;> assumption
  have heq : supp n N v = {S1, S2, S3, S4} := Finset.Subset.antisymm hsub hsup
  have hm := mass_eq_sum_supp n N v
  rw [heq, Finset.sum_insert (by simp [n12, n13, n14]),
    Finset.sum_insert (by simp [n23, n24]), Finset.sum_insert (by simp [n34]),
    Finset.sum_singleton] at hm
  exact four_vals_ne_eight (sq_cases (mem_supp.mp h1).2.2) (sq_cases (mem_supp.mp h2).2.2)
    (sq_cases (mem_supp.mp h3).2.2) (sq_cases (mem_supp.mp h4).2.2) (by rw [← hm]; exact h8)

/-! ## Reading a support set as a triple through a given vertex -/

/-- a support set at `v` in a cubic solution is `{v, x, y}` for two further vertices -/
lemma supp_tri_of_mem {n : ℕ} {N : ℕ → ℤ} (hcub : Cubic n N) {v S : ℕ}
    (hS : S ∈ supp n N v) :
    ∃ x y, x < n ∧ y < n ∧ x ≠ v ∧ y ≠ v ∧ x ≠ y ∧ S = tri v x y := by
  obtain ⟨hlt, hbit, hN⟩ := mem_supp.mp hS
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc, rfl⟩ :=
    exists_tri_of_card_three hlt (hcub S hlt hN)
  rcases mem_tri_iff.mp hbit with rfl | rfl | rfl
  · exact ⟨b, c, hb, hc, by omega, by omega, by omega, tri_ext (fun _ => by omega)⟩
  · exact ⟨a, c, ha, hc, by omega, by omega, by omega, tri_ext (fun _ => by omega)⟩
  · exact ⟨a, b, ha, hb, by omega, by omega, by omega, tri_ext (fun _ => by omega)⟩

/-! ## The octahedron at a support triple whose complement has all masses 4 -/

/-- The six-vertex octahedron with apex pair `(v, y)` and equator `a-b-a'-b'`:
the links of the five vertices other than `v` are completely determined. -/
def Octa (n : ℕ) (N : ℕ → ℤ) (v a b a' b' y : ℕ) : Prop :=
  LinkIs n N a b v b' y ∧ LinkIs n N b a v a' y ∧ LinkIs n N y b a b' a' ∧
    LinkIs n N a' b y b' v ∧ LinkIs n N b' v a y a'

/-- **Half-octahedron closure.**  If `{v, a, b}` is a support triple of a cubic solution in
which every vertex except possibly `v` has mass 4, then the octahedron on
`v, a, b, a', b', y` is forced: eight support triples, and the links of the five vertices
other than `v` are exactly the octahedron links (so those five vertices are exhausted). -/
theorem octa_eight {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hcub : Cubic n N)
    {v a b : ℕ} (hv : v < n) (ha : a < n) (hb : b < n)
    (hexc : ∀ w, w < n → w ≠ v → mass n N w = 4)
    (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b) (hF : N (tri v a b) ≠ 0) :
    ∃ a' b' y, a' < n ∧ b' < n ∧ y < n ∧
      a' ≠ v ∧ a' ≠ a ∧ a' ≠ b ∧ b' ≠ v ∧ b' ≠ a ∧ b' ≠ b ∧ a' ≠ b' ∧
      y ≠ v ∧ y ≠ a ∧ y ≠ b ∧ y ≠ a' ∧ y ≠ b' ∧ Octa n N v a b a' b' y := by
  have h4a : mass n N a = 4 := hexc a ha hav
  have h4b : mass n N b = 4 := hexc b hb hbv
  have hFa : N (tri a v b) ≠ 0 := by
    rw [show tri a v b = tri v a b from tri_ext (fun _ => by omega)]; exact hF
  obtain ⟨a', b', y, ha'lt, hb'lt, hylt, ha'a, ha'b, ha'v, ha'y, hb'a, hb'b, hb'v, hb'y,
    hya, hyb, hyv, hLa, hLb⟩ := octa_half hsol hcub hv ha hb h4a h4b hav hbv hab hFa
  have h4y : mass n N y = 4 := hexc y hylt hyv
  have h4a' : mass n N a' = 4 := hexc a' ha'lt ha'v
  have h4b' : mass n N b' = 4 := hexc b' hb'lt hb'v
  -- the four triples at `a` and at `b`
  have Favb' : N (tri a v b') ≠ 0 :=
    (hLa v b' hv hb'lt (Ne.symm hav) hb'a).mpr (edge_qr b v b' y)
  have Fab'y : N (tri a b' y) ≠ 0 :=
    (hLa b' y hb'lt hylt hb'a hya).mpr (edge_rs b v b' y)
  have Fayb : N (tri a y b) ≠ 0 :=
    (hLa y b hylt hb hya (Ne.symm hab)).mpr (edge_sp b v b' y)
  have Fbva' : N (tri b v a') ≠ 0 :=
    (hLb v a' hv ha'lt (Ne.symm hbv) ha'b).mpr (edge_qr a v a' y)
  have Fba'y : N (tri b a' y) ≠ 0 :=
    (hLb a' y ha'lt hylt ha'b hyb).mpr (edge_rs a v a' y)
  -- `a'` and `b'` are distinct: otherwise the link of `y` contains the triangle `a-a'-b`
  have ha'b' : a' ≠ b' := by
    intro hEq
    refine no_triangle_at hsol hcub hylt ha'lt ha hb h4y ha'y (Ne.symm hya) (Ne.symm hyb)
      hab ?_ ?_ ?_
    · rw [show tri y a' a = tri a b' y from tri_ext (fun _ => by omega)]; exact Fab'y
    · rw [show tri y a' b = tri b a' y from tri_ext (fun _ => by omega)]; exact Fba'y
    · rw [show tri y a b = tri a y b from tri_ext (fun _ => by omega)]; exact Fayb
  -- the link of `y` is the 4-cycle `b-a-b'-a'`
  have hLy : ∀ p q, p < n → q < n → p ≠ y → q ≠ y →
      (N (tri y p q) ≠ 0 ↔ Edge b a b' a' p q) := by
    refine link_of_three_faces hsol hcub hylt ha hb hb'lt ha'lt h4y (Ne.symm hya)
      (Ne.symm hyb) hb'y ha'y (Ne.symm hb'b) hab ha'a ?_ ?_ ?_
    · rw [show tri y a b = tri a y b from tri_ext (fun _ => by omega)]; exact Fayb
    · rw [show tri y a b' = tri a b' y from tri_ext (fun _ => by omega)]; exact Fab'y
    · rw [show tri y b a' = tri b a' y from tri_ext (fun _ => by omega)]; exact Fba'y
  have Fyb'a' : N (tri y b' a') ≠ 0 :=
    (hLy b' a' hb'lt ha'lt hb'y ha'y).mpr (edge_rs b a b' a')
  -- the link of `a'` is the 4-cycle `b-y-b'-v`
  have hLa' : ∀ p q, p < n → q < n → p ≠ a' → q ≠ a' →
      (N (tri a' p q) ≠ 0 ↔ Edge b y b' v p q) := by
    refine link_of_three_faces hsol hcub ha'lt hylt hb hb'lt hv h4a' (Ne.symm ha'y)
      (Ne.symm ha'b) (Ne.symm ha'b') (Ne.symm ha'v) (Ne.symm hb'b) hyb (Ne.symm hyv) ?_ ?_ ?_
    · rw [show tri a' y b = tri b a' y from tri_ext (fun _ => by omega)]; exact Fba'y
    · rw [show tri a' y b' = tri y b' a' from tri_ext (fun _ => by omega)]; exact Fyb'a'
    · rw [show tri a' b v = tri b v a' from tri_ext (fun _ => by omega)]; exact Fbva'
  have Fa'b'v : N (tri a' b' v) ≠ 0 :=
    (hLa' b' v hb'lt hv (Ne.symm ha'b') (Ne.symm ha'v)).mpr (edge_rs b y b' v)
  -- the link of `b'` is the 4-cycle `v-a-y-a'`
  have hLb' : ∀ p q, p < n → q < n → p ≠ b' → q ≠ b' →
      (N (tri b' p q) ≠ 0 ↔ Edge v a y a' p q) := by
    refine link_of_three_faces hsol hcub hb'lt ha hv hylt ha'lt h4b' (Ne.symm hb'a)
      (Ne.symm hb'v) (Ne.symm hb'y) ha'b' (Ne.symm hyv) hav ha'a ?_ ?_ ?_
    · rw [show tri b' a v = tri a v b' from tri_ext (fun _ => by omega)]; exact Favb'
    · rw [show tri b' a y = tri a b' y from tri_ext (fun _ => by omega)]; exact Fab'y
    · rw [show tri b' v a' = tri a' b' v from tri_ext (fun _ => by omega)]; exact Fa'b'v
  exact ⟨a', b', y, ha'lt, hb'lt, hylt, ha'v, ha'a, ha'b, hb'v, hb'a, hb'b, ha'b',
    hyv, hya, hyb, Ne.symm ha'y, Ne.symm hb'y, hLa, hLb, hLy, hLa', hLb'⟩

/-! ## The degree sequence at `n = 11`, `δ = 0` -/

/-- under `Cubic` the mass sum is exactly `3 · 16 = 48` -/
theorem cubic_sum_mass {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hcub : Cubic n N) :
    ∑ v ∈ range n, mass n N v = 48 := by
  rw [sum_mass]
  have h1 := hsol.2.1
  unfold CondI at h1
  have hcongr : ∑ S ∈ range (2 ^ n), (card n S : ℤ) * (N S) ^ 2
      = ∑ S ∈ range (2 ^ n), 3 * (N S) ^ 2 := by
    apply sum_congr rfl; intro S hS
    by_cases h0 : N S = 0
    · rw [h0]; ring
    · rw [hcub S (mem_range.mp hS) h0]; norm_num
  rw [hcongr, ← mul_sum, h1]; norm_num

/-- **The degree sequence.**  A cubic solution on eleven variables has masses `(8, 4^10)`
or `(6, 6, 4^9)`. -/
theorem eleven_degree_split {N : ℕ → ℤ} (hsol : IsSol 11 N) (hcub : Cubic 11 N) :
    (∃ v, v < 11 ∧ mass 11 N v = 8 ∧ ∀ w, w < 11 → w ≠ v → mass 11 N w = 4) ∨
    (∃ v w, v < 11 ∧ w < 11 ∧ v ≠ w ∧ mass 11 N v = 6 ∧ mass 11 N w = 6 ∧
      ∀ z, z < 11 → z ≠ v → z ≠ w → mass 11 N z = 4) := by
  have hzero : ∑ v ∈ (range 11).filter (fun v => ¬ ¬ mass 11 N v = 4),
      (mass 11 N v - 4) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [mem_filter] at hv
    rw [not_not.mp hv.2]; ring
  have htot : ∑ v ∈ range 11, (mass 11 N v - 4) = 4 := by
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, cubic_sum_mass hsol hcub]
    norm_num
  rw [← sum_filter_add_sum_filter_not (range 11) (fun v => ¬ mass 11 N v = 4),
    hzero, add_zero] at htot
  have hcard := card_mass_ne_four_le_two hsol
  have hcases : ((range 11).filter (fun v => ¬ mass 11 N v = 4)).card = 0 ∨
      ((range 11).filter (fun v => ¬ mass 11 N v = 4)).card = 1 ∨
      ((range 11).filter (fun v => ¬ mass 11 N v = 4)).card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [Finset.card_eq_zero] at h0
    rw [h0, Finset.sum_empty] at htot
    exact absurd htot (by norm_num)
  · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
    rw [hv, Finset.sum_singleton] at htot
    have hvmem : v ∈ (range 11).filter (fun v => ¬ mass 11 N v = 4) := by
      rw [hv]; exact Finset.mem_singleton_self v
    rw [mem_filter, mem_range] at hvmem
    refine Or.inl ⟨v, hvmem.1, by omega, ?_⟩
    intro w hw hwv
    by_contra hne
    have hmem : w ∈ (range 11).filter (fun v => ¬ mass 11 N v = 4) :=
      mem_filter.mpr ⟨mem_range.mpr hw, hne⟩
    rw [hv, Finset.mem_singleton] at hmem
    exact hwv hmem
  · obtain ⟨v, w, hvw, hpair⟩ := Finset.card_eq_two.mp h2
    rw [hpair, Finset.sum_pair hvw] at htot
    have hvmem : v ∈ (range 11).filter (fun u => ¬ mass 11 N u = 4) := by
      rw [hpair]; simp
    have hwmem : w ∈ (range 11).filter (fun u => ¬ mass 11 N u = 4) := by
      rw [hpair]; simp
    rw [mem_filter, mem_range] at hvmem hwmem
    have hcv := mass_cases hsol le_rfl hvmem.1
    have hcw := mass_cases hsol le_rfl hwmem.1
    refine Or.inr ⟨v, w, hvmem.1, hwmem.1, hvw, by omega, by omega, ?_⟩
    intro z hz hzv hzw
    by_contra hne
    have hmem : z ∈ (range 11).filter (fun u => ¬ mass 11 N u = 4) :=
      mem_filter.mpr ⟨mem_range.mpr hz, hne⟩
    rw [hpair] at hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact hzv h
    · exact hzw (Finset.mem_singleton.mp h)

/-! ## Reading off the triples at the apex `v` of an octahedron -/

/-- the six vertices of an octahedron are pairwise distinct -/
def Dist6 (v a b a' b' y : ℕ) : Prop :=
  v ≠ a ∧ v ≠ b ∧ v ≠ a' ∧ v ≠ b' ∧ v ≠ y ∧ a ≠ b ∧ a ≠ a' ∧ a ≠ b' ∧ a ≠ y ∧
    b ≠ a' ∧ b ≠ b' ∧ b ≠ y ∧ a' ≠ b' ∧ a' ≠ y ∧ b' ≠ y

/-- packaged form of `octa_eight` -/
theorem octa_eight' {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N) (hcub : Cubic n N)
    {v a b : ℕ} (hv : v < n) (ha : a < n) (hb : b < n)
    (hexc : ∀ w, w < n → w ≠ v → mass n N w = 4)
    (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b) (hF : N (tri v a b) ≠ 0) :
    ∃ a' b' y, a' < n ∧ b' < n ∧ y < n ∧ Dist6 v a b a' b' y ∧
      Octa n N v a b a' b' y := by
  obtain ⟨a', b', y, ha'lt, hb'lt, hylt, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11,
    e12, hO⟩ := octa_eight hsol hcub hv ha hb hexc hav hbv hab hF
  exact ⟨a', b', y, ha'lt, hb'lt, hylt,
    ⟨Ne.symm hav, Ne.symm hbv, Ne.symm e1, Ne.symm e4, Ne.symm e8, hab, Ne.symm e2,
      Ne.symm e5, Ne.symm e9, Ne.symm e3, Ne.symm e6, Ne.symm e10, e7, Ne.symm e11,
      Ne.symm e12⟩, hO⟩

/-- rotating the link cycle -/
lemma linkIs_rot {n : ℕ} {N : ℕ → ℤ} {x p q r s : ℕ} (h : LinkIs n N x p q r s) :
    LinkIs n N x q r s p :=
  fun u t hu ht hux htx => (h u t hu ht hux htx).trans edge_rot

/-- if `q` is on the link cycle of `x`, the support triples `{x, q, z}` have `z` one of the
two cycle-neighbours of `q` -/
lemma link_v_nbrs {n : ℕ} {N : ℕ → ℤ} {x p q r s z : ℕ} (hL : LinkIs n N x p q r s)
    (hp : p < n) (hq : q < n) (hr : r < n) (hs : s < n) (hz : z < n)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hqx : q ≠ x) (hzx : z ≠ x) (hF : N (tri x q z) ≠ 0) : z = p ∨ z = r := by
  have E : Edge p q r s q z := (hL q z hq hz hqx hzx).mp hF
  have k := edge_nbr hpq hpr hps hqr hqs hrs E
  clear * - k hpq hpr hps hqr hqs hrs
  omega

/-- a vertex off the link cycle of `x` is in no support triple with `x` -/
lemma link_not_mem {n : ℕ} {N : ℕ → ℤ} {x p q r s w z : ℕ} (hL : LinkIs n N x p q r s)
    (hw : w < n) (hz : z < n) (hwx : w ≠ x) (hzx : z ≠ x)
    (hwp : w ≠ p) (hwq : w ≠ q) (hwr : w ≠ r) (hws : w ≠ s)
    (hF : N (tri x w z) ≠ 0) : False := by
  have E : Edge p q r s w z := (hL w z hw hz hwx hzx).mp hF
  have k := (edge_mem E).1
  clear * - k hwp hwq hwr hws
  omega

/-- **The triples at the apex.**  In the octahedron `v, a, b, a', b', y`, any support triple
`{v, x, z}` whose middle vertex `x` lies on the equator or is the antipode `y` is one of the
four equatorial triples at `v`. -/
theorem octa_v_triple {n : ℕ} {N : ℕ → ℤ} {v a b a' b' y : ℕ}
    (hv : v < n) (ha : a < n) (hb : b < n) (ha'lt : a' < n) (hb'lt : b' < n) (hylt : y < n)
    (hD : Dist6 v a b a' b' y) (hO : Octa n N v a b a' b' y)
    {x z : ℕ} (hx : x < n) (hz : z < n) (hxv : x ≠ v) (hzv : z ≠ v) (hxz : x ≠ z)
    (hmem : x = a ∨ x = b ∨ x = a' ∨ x = b' ∨ x = y)
    (hF : N (tri v x z) ≠ 0) :
    tri v x z = tri v a b ∨ tri v x z = tri v a b' ∨ tri v x z = tri v a' b ∨
      tri v x z = tri v a' b' := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15⟩ := hD
  obtain ⟨hLa, hLb, hLy, hLa', hLb'⟩ := hO
  have hF' : N (tri x v z) ≠ 0 := by rw [tri_swap x v z]; exact hF
  clear hF
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · have h2 : z = b ∨ z = b' :=
      link_v_nbrs hLa hb hv hb'lt hylt hz (Ne.symm d2) d11 d12 d4 d5 d15 d1
        (Ne.symm hxz) hF'
    rcases h2 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · have h2 : z = a ∨ z = a' :=
      link_v_nbrs hLb ha hv ha'lt hylt hz (Ne.symm d1) d7 d9 d3 d5 d14 d2
        (Ne.symm hxz) hF'
    rcases h2 with rfl | rfl
    · exact Or.inl (tri_swap23 _ _ _)
    · exact Or.inr (Or.inr (Or.inl (tri_swap23 _ _ _)))
  · have h2 : z = b' ∨ z = b :=
      link_v_nbrs (linkIs_rot (linkIs_rot hLa')) hb'lt hv hb hylt hz (Ne.symm d4)
        (Ne.symm d11) d15 d2 d5 d12 d3 (Ne.symm hxz) hF'
    rcases h2 with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))
  · have h2 : z = a' ∨ z = a :=
      link_v_nbrs (linkIs_rot (linkIs_rot (linkIs_rot hLb'))) ha'lt hv ha hylt hz
        (Ne.symm d3) (Ne.symm d7) d14 d1 d5 d9 d4 (Ne.symm hxz) hF'
    rcases h2 with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (tri_swap23 _ _ _)))
    · exact Or.inr (Or.inl (tri_swap23 _ _ _))
  · exact (link_not_mem hLy hv hz d5 (Ne.symm hxz) d2 d1 d4 d3 hF').elim

/-! ## Condition (ii) in correlation form -/

/-- `CondII` says exactly that every shifted autocorrelation of `N` vanishes. -/
lemma condII_corr {n : ℕ} {N : ℕ → ℤ} (h2 : CondII n N) {U : ℕ} (hU : 0 < U)
    (hUlt : U < 2 ^ n) : ∑ S ∈ range (2 ^ n), N S * N (S ^^^ U) = 0 := by
  have key : ∀ S ∈ range (2 ^ n),
      (∑ T ∈ range (2 ^ n), if S ^^^ T = U then N S * N T else 0) = N S * N (S ^^^ U) := by
    intro S hS
    have hstep : (∑ T ∈ range (2 ^ n), if S ^^^ T = U then N S * N T else 0)
        = ∑ T ∈ range (2 ^ n), if T = S ^^^ U then N S * N T else 0 := by
      apply sum_congr rfl; intro T _
      have hEq : (S ^^^ T = U) ↔ (T = S ^^^ U) := by
        constructor
        · rintro rfl; rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
        · rintro rfl; rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      simp only [hEq]
    rw [hstep, Finset.sum_ite_eq' (range (2 ^ n)) (S ^^^ U) (fun T => N S * N T),
      if_pos (xor_mem_range hS (mem_range.mpr hUlt))]
  rw [← h2 U hU hUlt]
  exact (sum_congr rfl key).symm

/-- half of the autocorrelation: the terms whose first set contains `y` -/
lemma corr_bit_half {n : ℕ} {N : ℕ → ℤ} {U y : ℕ} (hyU : U.testBit y = true)
    (hUlt : U < 2 ^ n) (hsum : ∑ S ∈ range (2 ^ n), N S * N (S ^^^ U) = 0) :
    ∑ S ∈ (range (2 ^ n)).filter (fun S => S.testBit y = true), N S * N (S ^^^ U) = 0 := by
  have hxorlt : ∀ S, S < 2 ^ n → S ^^^ U < 2 ^ n := fun S hS =>
    mem_range.mp (xor_mem_range (mem_range.mpr hS) (mem_range.mpr hUlt))
  have hsplit := Finset.sum_filter_add_sum_filter_not (range (2 ^ n))
    (fun S => S.testBit y = true) (fun S => N S * N (S ^^^ U))
  have hbij : ∑ S ∈ (range (2 ^ n)).filter (fun S => ¬ S.testBit y = true),
        N S * N (S ^^^ U)
      = ∑ S ∈ (range (2 ^ n)).filter (fun S => S.testBit y = true), N S * N (S ^^^ U) := by
    refine Finset.sum_nbij' (fun S => S ^^^ U) (fun S => S ^^^ U) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      rw [mem_filter, mem_range] at hS
      have hb : S.testBit y = false := by
        cases hc : S.testBit y with
        | false => rfl
        | true => exact absurd hc hS.2
      rw [mem_filter, mem_range]
      exact ⟨hxorlt S hS.1, by rw [Nat.testBit_xor, hb, hyU]; rfl⟩
    · intro S hS
      rw [mem_filter, mem_range] at hS
      rw [mem_filter, mem_range]
      refine ⟨hxorlt S hS.1, ?_⟩
      rw [Nat.testBit_xor, hS.2, hyU]
      simp
    · intro S _
      show (S ^^^ U) ^^^ U = S
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · intro S _
      show (S ^^^ U) ^^^ U = S
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · intro S _
      show N S * N (S ^^^ U) = N (S ^^^ U) * N ((S ^^^ U) ^^^ U)
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, mul_comm]
  rw [hsum] at hsplit
  rw [hbij] at hsplit
  linarith

/-! ## Bitmask identities for the octahedron -/

lemma pair_eq_tri (v y : ℕ) : pair v y = tri v y y := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Bool.eq_iff_iff, mem_pair_iff, mem_tri_iff]; tauto

lemma pair_lt {n v y : ℕ} (hv : v < n) (hy : y < n) : pair v y < 2 ^ n := by
  rw [pair_eq_tri]; exact tri_lt hv hy hy

/-- flipping the apex: `{y, p, q} Δ {v, y} = {v, p, q}` -/
lemma tri_xor_pair {v y p q : ℕ} (hpy : p ≠ y) (hqy : q ≠ y) (hpv : p ≠ v) (hqv : q ≠ v)
    (hvy : v ≠ y) : tri y p q ^^^ pair v y = tri v p q := by
  have h1 : tri y p q ^^^ 2 ^ y = pair p q := tri_xor_two_pow hpy hqy
  have h2 : tri v p q ^^^ 2 ^ v = pair p q := tri_xor_two_pow hpv hqv
  rw [← two_pow_xor_two_pow hvy, Nat.xor_comm (2 ^ v), ← Nat.xor_assoc, h1, ← h2,
    Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- two triples differ if one has a vertex the other lacks -/
lemma tri_ne_of_mem {x u1 u2 u3 w1 w2 w3 : ℕ} (h1 : x ≠ u1) (h2 : x ≠ u2) (h3 : x ≠ u3)
    (hmem : x = w1 ∨ x = w2 ∨ x = w3) : tri u1 u2 u3 ≠ tri w1 w2 w3 := by
  intro h
  have hb : (tri u1 u2 u3).testBit x = true := by rw [h]; exact mem_tri_iff.mpr hmem
  rcases mem_tri_iff.mp hb with rfl | rfl | rfl
  · exact h1 rfl
  · exact h2 rfl
  · exact h3 rfl


/-! ## The octahedron is impossible when its rim has mass 4 -/

lemma tri_mem_supp2 {n : ℕ} {N : ℕ → ℤ} {x y z : ℕ} (hx : x < n) (hy : y < n)
    (hz : z < n) (h : N (tri x y z) ≠ 0) : tri x y z ∈ supp n N y :=
  mem_supp.mpr ⟨tri_lt hx hy hz, mem_tri_iff.mpr (Or.inr (Or.inl rfl)), h⟩

lemma tri_mem_supp3 {n : ℕ} {N : ℕ → ℤ} {x y z : ℕ} (hx : x < n) (hy : y < n)
    (hz : z < n) (h : N (tri x y z) ≠ 0) : tri x y z ∈ supp n N z :=
  mem_supp.mpr ⟨tri_lt hx hy hz, mem_tri_iff.mpr (Or.inr (Or.inr rfl)), h⟩

lemma pm_mul {p q : ℤ} (hp : p = 1 ∨ p = -1) (hq : q = 1 ∨ q = -1) :
    p * q = 1 ∨ p * q = -1 := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> norm_num

/-- the sign contradiction: four `±1` values, pairwise linked and summing to zero -/
lemma eps_kill {e1 e2 e3 e4 : ℤ} (h1 : e1 = 1 ∨ e1 = -1) (h2 : e2 = 1 ∨ e2 = -1)
    (h3 : e3 = 1 ∨ e3 = -1) (h4 : e4 = 1 ∨ e4 = -1)
    (p12 : e1 * e2 = 1) (p14 : e1 * e4 = 1) (p34 : e3 * e4 = 1)
    (hsum : e1 + e2 + e3 + e4 = 0) : False := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;>
    rcases h4 with rfl | rfl <;> omega

/-- **The octahedron kill.**  If `v, a, b, a', b', y` carry the octahedron links and the rim
vertices `a, b, a'` and the antipode `y` all have mass 4, condition (ii) at the pair
`{v, y}` fails.  (The mass of `v` itself is irrelevant.) -/
theorem octa_kill {n : ℕ} {N : ℕ → ℤ} (hsol : IsSol n N)
    {v a b a' b' y : ℕ} (hv : v < n) (ha : a < n) (hb : b < n) (ha'lt : a' < n)
    (hb'lt : b' < n) (hylt : y < n)
    (h4a : mass n N a = 4) (h4b : mass n N b = 4) (h4a' : mass n N a' = 4)
    (h4y : mass n N y = 4)
    (hD : Dist6 v a b a' b' y) (hO : Octa n N v a b a' b' y) : False := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15⟩ := hD
  obtain ⟨hLa, hLb, hLy, hLa', hLb'⟩ := hO
  -- the four support triples at `y`
  have Y1 : N (tri y a b) ≠ 0 :=
    (hLy a b ha hb d9 d12).mpr (edge_symm.mp (edge_pq b a b' a'))
  have Y2 : N (tri y a b') ≠ 0 := (hLy a b' ha hb'lt d9 d15).mpr (edge_qr b a b' a')
  have Y3 : N (tri y a' b') ≠ 0 :=
    (hLy a' b' ha'lt hb'lt d14 d15).mpr (edge_symm.mp (edge_rs b a b' a'))
  have Y4 : N (tri y a' b) ≠ 0 := (hLy a' b ha'lt hb d14 d12).mpr (edge_sp b a b' a')
  -- the four support triples at `v`
  have V1 : N (tri v a b) ≠ 0 := by
    rw [← tri_rotr a b v]; exact (hLa b v hb hv (Ne.symm d6) d1).mpr (edge_pq b v b' y)
  have V2 : N (tri v a b') ≠ 0 := by
    rw [← tri_swap a v b']; exact (hLa v b' hv hb'lt d1 (Ne.symm d8)).mpr (edge_qr b v b' y)
  have V4 : N (tri v a' b) ≠ 0 := by
    rw [← tri_rotl b v a']; exact (hLb v a' hv ha'lt d2 (Ne.symm d10)).mpr (edge_qr a v a' y)
  have V3 : N (tri v a' b') ≠ 0 := by
    rw [← tri_rotr a' b' v]
    exact (hLa' b' v hb'lt hv (Ne.symm d13) d3).mpr (edge_rs b y b' v)
  clear hLa hLb hLy hLa' hLb'
  -- the support of `y`
  have hsy : supp n N y = {tri y a b, tri y a b', tri y a' b', tri y a' b} :=
    supp_eq_quad h4y (tri_mem_supp hylt ha hb Y1) (tri_mem_supp hylt ha hb'lt Y2)
      (tri_mem_supp hylt ha'lt hb'lt Y3) (tri_mem_supp hylt ha'lt hb Y4)
      (tri_ne_of_mem d15 (Ne.symm d8) (Ne.symm d11) (Or.inr (Or.inr rfl)))
      (tri_ne_of_mem d14 (Ne.symm d7) (Ne.symm d10) (Or.inr (Or.inl rfl)))
      (tri_ne_of_mem d14 (Ne.symm d7) (Ne.symm d10) (Or.inr (Or.inl rfl)))
      (tri_ne_of_mem d14 (Ne.symm d7) d13 (Or.inr (Or.inl rfl)))
      (tri_ne_of_mem d14 (Ne.symm d7) d13 (Or.inr (Or.inl rfl)))
      (tri_ne_of_mem d12 d10 d11 (Or.inr (Or.inr rfl)))
  -- the support of `a`
  have hsa : supp n N a = {tri v a b, tri v a b', tri y a b', tri y a b} :=
    supp_eq_quad h4a (tri_mem_supp2 hv ha hb V1) (tri_mem_supp2 hv ha hb'lt V2)
      (tri_mem_supp2 hylt ha hb'lt Y2) (tri_mem_supp2 hylt ha hb Y1)
      (tri_ne_of_mem (Ne.symm d4) (Ne.symm d8) (Ne.symm d11) (Or.inr (Or.inr rfl)))
      (tri_ne_of_mem (Ne.symm d5) (Ne.symm d9) (Ne.symm d12) (Or.inl rfl))
      (tri_ne_of_mem (Ne.symm d5) (Ne.symm d9) (Ne.symm d12) (Or.inl rfl))
      (tri_ne_of_mem (Ne.symm d5) (Ne.symm d9) (Ne.symm d15) (Or.inl rfl))
      (tri_ne_of_mem (Ne.symm d5) (Ne.symm d9) (Ne.symm d15) (Or.inl rfl))
      (tri_ne_of_mem d12 (Ne.symm d6) d11 (Or.inr (Or.inr rfl)))
  -- the support of `b`
  have hsb : supp n N b = {tri v a b, tri v a' b, tri y a' b, tri y a b} :=
    supp_eq_quad h4b (tri_mem_supp3 hv ha hb V1) (tri_mem_supp3 hv ha'lt hb V4)
      (tri_mem_supp3 hylt ha'lt hb Y4) (tri_mem_supp3 hylt ha hb Y1)
      (tri_ne_of_mem (Ne.symm d3) (Ne.symm d7) (Ne.symm d10) (Or.inr (Or.inl rfl)))
      (tri_ne_of_mem (Ne.symm d5) (Ne.symm d9) (Ne.symm d12) (Or.inl rfl))
      (tri_ne_of_mem (Ne.symm d5) (Ne.symm d9) (Ne.symm d12) (Or.inl rfl))
      (tri_ne_of_mem (Ne.symm d5) (Ne.symm d14) (Ne.symm d12) (Or.inl rfl))
      (tri_ne_of_mem (Ne.symm d5) (Ne.symm d14) (Ne.symm d12) (Or.inl rfl))
      (tri_ne_of_mem d9 d7 d6 (Or.inr (Or.inl rfl)))
  -- the support of `a'`
  have hsa' : supp n N a' = {tri v a' b', tri v a' b, tri y a' b, tri y a' b'} :=
    supp_eq_quad h4a' (tri_mem_supp2 hv ha'lt hb'lt V3) (tri_mem_supp2 hv ha'lt hb V4)
      (tri_mem_supp2 hylt ha'lt hb Y4) (tri_mem_supp2 hylt ha'lt hb'lt Y3)
      (tri_ne_of_mem (Ne.symm d2) d10 d11 (Or.inr (Or.inr rfl)))
      (tri_ne_of_mem (Ne.symm d5) (Ne.symm d14) (Ne.symm d15) (Or.inl rfl))
      (tri_ne_of_mem (Ne.symm d5) (Ne.symm d14) (Ne.symm d15) (Or.inl rfl))
      (tri_ne_of_mem (Ne.symm d5) (Ne.symm d14) (Ne.symm d12) (Or.inl rfl))
      (tri_ne_of_mem (Ne.symm d5) (Ne.symm d14) (Ne.symm d12) (Or.inl rfl))
      (tri_ne_of_mem d15 (Ne.symm d13) (Ne.symm d11) (Or.inr (Or.inr rfl)))
  -- the three coefficient products
  have Pa := (mass_four hsol ha h4a
    (tri_ne_of_mem (Ne.symm d4) (Ne.symm d8) (Ne.symm d11) (Or.inr (Or.inr rfl)))
    (tri_ne_of_mem (Ne.symm d5) (Ne.symm d9) (Ne.symm d12) (Or.inl rfl))
    (tri_ne_of_mem (Ne.symm d5) (Ne.symm d9) (Ne.symm d12) (Or.inl rfl))
    (tri_ne_of_mem (Ne.symm d5) (Ne.symm d9) (Ne.symm d15) (Or.inl rfl))
    (tri_ne_of_mem (Ne.symm d5) (Ne.symm d9) (Ne.symm d15) (Or.inl rfl))
    (tri_ne_of_mem d12 (Ne.symm d6) d11 (Or.inr (Or.inr rfl))) hsa).2
  have Pb := (mass_four hsol hb h4b
    (tri_ne_of_mem (Ne.symm d3) (Ne.symm d7) (Ne.symm d10) (Or.inr (Or.inl rfl)))
    (tri_ne_of_mem (Ne.symm d5) (Ne.symm d9) (Ne.symm d12) (Or.inl rfl))
    (tri_ne_of_mem (Ne.symm d5) (Ne.symm d9) (Ne.symm d12) (Or.inl rfl))
    (tri_ne_of_mem (Ne.symm d5) (Ne.symm d14) (Ne.symm d12) (Or.inl rfl))
    (tri_ne_of_mem (Ne.symm d5) (Ne.symm d14) (Ne.symm d12) (Or.inl rfl))
    (tri_ne_of_mem d9 d7 d6 (Or.inr (Or.inl rfl))) hsb).2
  have Pa' := (mass_four hsol ha'lt h4a'
    (tri_ne_of_mem (Ne.symm d2) d10 d11 (Or.inr (Or.inr rfl)))
    (tri_ne_of_mem (Ne.symm d5) (Ne.symm d14) (Ne.symm d15) (Or.inl rfl))
    (tri_ne_of_mem (Ne.symm d5) (Ne.symm d14) (Ne.symm d15) (Or.inl rfl))
    (tri_ne_of_mem (Ne.symm d5) (Ne.symm d14) (Ne.symm d12) (Or.inl rfl))
    (tri_ne_of_mem (Ne.symm d5) (Ne.symm d14) (Ne.symm d12) (Or.inl rfl))
    (tri_ne_of_mem d15 (Ne.symm d13) (Ne.symm d11) (Or.inr (Or.inr rfl))) hsa').2
  -- the ±1 facts
  have pmy := mass_four_pm hsol hylt h4y
  have pma := mass_four_pm hsol ha h4a
  have pma' := mass_four_pm hsol ha'lt h4a'
  have qY1 := pmy _ (tri_mem_supp hylt ha hb Y1)
  have qY2 := pmy _ (tri_mem_supp hylt ha hb'lt Y2)
  have qY3 := pmy _ (tri_mem_supp hylt ha'lt hb'lt Y3)
  have qY4 := pmy _ (tri_mem_supp hylt ha'lt hb Y4)
  have qV1 := pma _ (tri_mem_supp2 hv ha hb V1)
  have qV2 := pma _ (tri_mem_supp2 hv ha hb'lt V2)
  have qV3 := pma' _ (tri_mem_supp2 hv ha'lt hb'lt V3)
  have qV4 := pma' _ (tri_mem_supp2 hv ha'lt hb V4)
  -- condition (ii) at the pair {v, y}
  have hUlt : pair v y < 2 ^ n := pair_lt hv hylt
  have hUpos : 0 < pair v y := Nat.pos_of_ne_zero pair_ne_zero
  have hyU : (pair v y).testBit y = true := mem_pair_iff.mpr (Or.inr rfl)
  have hhalf := corr_bit_half hyU hUlt (condII_corr hsol.2.2.1 hUpos hUlt)
  have hsub : supp n N y ⊆ (range (2 ^ n)).filter (fun S => S.testBit y = true) := by
    intro S hS
    obtain ⟨k1, k2, k3⟩ := mem_supp.mp hS
    exact mem_filter.mpr ⟨mem_range.mpr k1, k2⟩
  have hvanish : ∀ S ∈ (range (2 ^ n)).filter (fun S => S.testBit y = true),
      S ∉ supp n N y → N S * N (S ^^^ pair v y) = 0 := by
    intro S hS hnot
    rw [mem_filter, mem_range] at hS
    have h0 : N S = 0 := by
      by_contra hne
      exact hnot (mem_supp.mpr ⟨hS.1, hS.2, hne⟩)
    rw [h0, zero_mul]
  rw [← Finset.sum_subset hsub hvanish, hsy,
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨tri_ne_of_mem d15 (Ne.symm d8) (Ne.symm d11) (Or.inr (Or.inr rfl)),
        tri_ne_of_mem d14 (Ne.symm d7) (Ne.symm d10) (Or.inr (Or.inl rfl)),
        tri_ne_of_mem d14 (Ne.symm d7) (Ne.symm d10) (Or.inr (Or.inl rfl))⟩),
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨tri_ne_of_mem d14 (Ne.symm d7) d13 (Or.inr (Or.inl rfl)),
        tri_ne_of_mem d14 (Ne.symm d7) d13 (Or.inr (Or.inl rfl))⟩),
    Finset.sum_insert (by
      simp only [Finset.mem_singleton]
      exact tri_ne_of_mem d12 d10 d11 (Or.inr (Or.inr rfl))),
    Finset.sum_singleton,
    tri_xor_pair d9 d12 (Ne.symm d1) (Ne.symm d2) d5,
    tri_xor_pair d9 d15 (Ne.symm d1) (Ne.symm d4) d5,
    tri_xor_pair d14 d15 (Ne.symm d3) (Ne.symm d4) d5,
    tri_xor_pair d14 d12 (Ne.symm d3) (Ne.symm d2) d5] at hhalf
  exact eps_kill (pm_mul qV1 qY1) (pm_mul qV2 qY2) (pm_mul qV3 qY3) (pm_mul qV4 qY4)
    (by linear_combination Pa) (by linear_combination Pb) (by linear_combination Pa')
    (by linear_combination hhalf)


/-! ## The `(8, 4^10)` branch of `δ = 0` -/

/-- **The `(8, 4^10)` sub-case is impossible.**  If at most one vertex `v` of a cubic
solution has mass different from 4, take any support triple at `v`: `octa_eight` closes it
into an octahedron whose rim and antipode all have mass 4, and `octa_kill` contradicts
condition (ii).  (The mass of `v` is never used.) -/
theorem eleven_delta_zero_eight {N : ℕ → ℤ} (hsol : IsSol 11 N) (hcub : Cubic 11 N)
    {v : ℕ} (hv : v < 11) (hexc : ∀ w, w < 11 → w ≠ v → mass 11 N w = 4) : False := by
  obtain ⟨S, hS⟩ := supp_nonempty hsol hv
  obtain ⟨a, b, ha, hb, hav, hbv, hab, rfl⟩ := supp_tri_of_mem hcub hS
  have hF : N (tri v a b) ≠ 0 := (mem_supp.mp hS).2.2
  obtain ⟨a', b', y, ha'lt, hb'lt, hylt, hD, hO⟩ :=
    octa_eight' hsol hcub hv ha hb hexc hav hbv hab hF
  exact octa_kill hsol hv ha hb ha'lt hb'lt hylt (hexc a ha hav) (hexc b hb hbv)
    (hexc a' ha'lt (Ne.symm hD.2.2.1)) (hexc y hylt (Ne.symm hD.2.2.2.2.1)) hD hO

/-- **Reduction of the `δ = 0` case.**  A cubic solution on eleven variables must have the
degree sequence `(6, 6, 4^9)`: the `(8, 4^10)` alternative is closed. -/
theorem eleven_delta_zero_reduce {N : ℕ → ℤ} (hsol : IsSol 11 N) (hcub : Cubic 11 N) :
    ∃ v w, v < 11 ∧ w < 11 ∧ v ≠ w ∧ mass 11 N v = 6 ∧ mass 11 N w = 6 ∧
      ∀ z, z < 11 → z ≠ v → z ≠ w → mass 11 N z = 4 := by
  rcases eleven_degree_split hsol hcub with ⟨v, hv, _, hexc⟩ | h
  · exact (eleven_delta_zero_eight hsol hcub hv hexc).elim
  · exact h

end R3
