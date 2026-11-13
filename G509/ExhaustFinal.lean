/-
Copyright (c) 2026 olivierFer3. Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Exhaust
import G509.X.R0
import G509.X.R1
import G509.X.R2
import G509.X.R3
import G509.X.R4
import G509.X.R5
import G509.X.R6
import G509.X.R7
import G509.X.R8
import G509.X.R9
import G509.X.R10
import G509.X.R11
import G509.X.R12
import G509.X.R13
import G509.X.R14
import G509.X.R15
import Mathlib.Tactic.IntervalCases

/-!
# G509: exhaustiveness of the edges

`G509.EX.edges_exhaustive`: for `i, j < 509`, the points `P i` and `P j` are at distance exactly 1
if and only if `(i, j)` or `(j, i)` is in the list `edges` (2442 entries). Together with `S_card`
(509 distinct points), the unit-distance edges among the 509 points of G509 are thus exactly the pairs
listed in `edges`. Proof: integer boxes (`G509/Exhaust.lean`, `far_sound`), rows checked by the
kernel (`G509/X/R*.lean`), adjacency `adjN` equal to `edges` (`flat_eq`, kernel).
-/

namespace G509.EX

theorem flat_eq : flat adjN 0 = edges := by decide +kernel

theorem boxes_length : boxes.length = 509 := by decide +kernel
theorem adjN_length : adjN.length = 509 := by decide +kernel

theorem chunks_ok : ∀ k, k < 16 → rowsOK (boxes.drop (32 * k)) (32 * k) (adjN.drop (32 * k)) 32 = true := by
  intro k hk
  interval_cases k
  · exact rows_0
  · exact rows_1
  · exact rows_2
  · exact rows_3
  · exact rows_4
  · exact rows_5
  · exact rows_6
  · exact rows_7
  · exact rows_8
  · exact rows_9
  · exact rows_10
  · exact rows_11
  · exact rows_12
  · exact rows_13
  · exact rows_14
  · exact rows_15

lemma getD_drop' {α : Type} (l : List α) (a b : ℕ) (d : α) : (l.drop a).getD b d = l.getD (a + b) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

lemma drop_drop' {α : Type} (l : List α) (a b : ℕ) : (l.drop a).drop b = l.drop (a + b) := by
  rw [List.drop_drop]

theorem row_ok (i : ℕ) (hi : i < 509) :
    rowOK (boxes.getD i (0, 0, 0, 0)) (boxes.drop (i + 1)) (i + 1) (adjN.getD i []) = true := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 32 ∧ i = 32 * q + r :=
    ⟨i / 32, i % 32, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod i 32).symm⟩
  have h := rowsOK_sound _ _ _ _ (chunks_ok q (by omega)) r hr
    (by rw [List.length_drop, boxes_length]; omega)
  rw [getD_drop', getD_drop', drop_drop', show 32 * q + (r + 1) = 32 * q + r + 1 by omega] at h
  exact h

theorem box_P (i : ℕ) : boxes.getD i (0, 0, 0, 0) = boxOf (pts.getD i default) ∨ boxes.length ≤ i := by
  by_cases h : i < 509
  · left
    rw [boxes_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
    have hl : i < pts.length := by rw [pts_length]; exact h
    simp [List.getElem?_eq_getElem hl]
  · right; rw [boxes_length]; omega

theorem unit_imp_edge (i j : ℕ) (hij : i < j) (hj : j < 509) (hu : unitDistance (P i) (P j)) :
    (i, j) ∈ edges := by
  have hr := rowOK_sound _ _ _ _ (row_ok i (by omega)) (j - i - 1)
    (by rw [List.length_drop, boxes_length]; omega)
  rw [show i + 1 + (j - i - 1) = j by omega] at hr
  rcases hr with h | h
  · have := flat_mem adjN 0 i j h
    rw [Nat.zero_add, flat_eq] at this
    exact this
  · exfalso
    rw [getD_drop', show i + 1 + (j - i - 1) = j by omega] at h
    rcases box_P i with hi | hi
    · rcases box_P j with hj' | hj'
      · rw [hi, hj'] at h
        exact far_sound _ _ h hu
      · rw [boxes_length] at hj'; omega
    · rw [boxes_length] at hi; omega

/-- Exhaustiveness: `P i`, `P j` (i, j < 509) are at distance 1 iff `{i, j}` is an edge of `edges`. -/
theorem edges_exhaustive (i j : ℕ) (hi : i < 509) (hj : j < 509) :
    unitDistance (P i) (P j) ↔ (i, j) ∈ edges ∨ (j, i) ∈ edges := by
  constructor
  · intro hu
    rcases lt_trichotomy i j with h | h | h
    · exact Or.inl (unit_imp_edge i j h hj hu)
    · subst h
      unfold unitDistance at hu
      rw [sub_self, norm_zero] at hu
      exact absurd hu (by norm_num)
    · right
      apply unit_imp_edge j i h hi
      unfold unitDistance at hu ⊢
      rw [norm_sub_rev]; exact hu
  · rintro (h | h)
    · exact unit_edges (i, j) h
    · have : unitDistance (P j) (P i) := unit_edges (j, i) h
      unfold unitDistance at this ⊢
      rw [norm_sub_rev]; exact this

end G509.EX

#print axioms G509.EX.edges_exhaustive
