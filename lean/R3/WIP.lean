import Mathlib
/-! Scratch: benchmark of the Edge combinatorics (NOT imported by R3.lean). -/
namespace R3WIP

def Edge (p q r s x y : ℕ) : Prop :=
  (x = p ∧ y = q) ∨ (x = q ∧ y = p) ∨ (x = q ∧ y = r) ∨ (x = r ∧ y = q) ∨
  (x = r ∧ y = s) ∨ (x = s ∧ y = r) ∨ (x = s ∧ y = p) ∨ (x = p ∧ y = s)

set_option maxHeartbeats 400000 in
lemma edge_symm {p q r s x y : ℕ} : Edge p q r s x y ↔ Edge p q r s y x := by
  unfold Edge; omega

lemma edge_symm' {p q r s x y : ℕ} : Edge p q r s x y ↔ Edge p q r s y x := by
  unfold Edge; tauto

/-- dihedral: reversed and rotated cycle has the same edges -/
lemma edge_dihedral {y1 y2 y3 y4 y z : ℕ} :
    Edge y2 y1 y4 y3 y z ↔ Edge y1 y2 y3 y4 y z := by
  unfold Edge; omega

lemma edge_dihedral' {y1 y2 y3 y4 y z : ℕ} :
    Edge y2 y1 y4 y3 y z ↔ Edge y1 y2 y3 y4 y z := by
  unfold Edge; tauto

/-- no triangles in a 4-cycle -/
lemma edge_no_triangle {p q r s a v c : ℕ}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (h1 : Edge p q r s a v) (h2 : Edge p q r s v c) (h3 : Edge p q r s a c) : False := by
  unfold Edge at h1 h2 h3
  omega

/-- two edges at v: the cycle is b-v-d-x -/
lemma edge_through {p q r s v b d : ℕ}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (h1 : Edge p q r s v b) (h2 : Edge p q r s v d) (hbd : b ≠ d) :
    ∃ x, x ≠ v ∧ x ≠ b ∧ x ≠ d ∧ (x = p ∨ x = q ∨ x = r ∨ x = s) ∧
      ∀ y z, Edge p q r s y z ↔ Edge b v d x y z := by
  unfold Edge at h1 h2
  rcases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
  rcases h2 with ⟨e3, e4⟩ | ⟨e3, e4⟩ | ⟨e3, e4⟩ | ⟨e3, e4⟩ | ⟨e3, e4⟩ | ⟨e3, e4⟩ | ⟨e3, e4⟩ | ⟨e3, e4⟩ <;>
  first
  | (exfalso; omega)
  | (refine ⟨p, by omega, by omega, by omega, by omega, fun y z => ?_⟩; unfold Edge; omega)
  | (refine ⟨q, by omega, by omega, by omega, by omega, fun y z => ?_⟩; unfold Edge; omega)
  | (refine ⟨r, by omega, by omega, by omega, by omega, fun y z => ?_⟩; unfold Edge; omega)
  | (refine ⟨s, by omega, by omega, by omega, by omega, fun y z => ?_⟩; unfold Edge; omega)

end R3WIP
