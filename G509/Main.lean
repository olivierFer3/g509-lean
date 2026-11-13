/-
Copyright (c) 2026 olivierFer3. Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Defs
import G509.Edges0
import G509.Edges1
import G509.Edges2
import G509.Edges3
import G509.Edges4
import G509.Edges5
import G509.Edges6
import G509.Edges7
import G509.Edges8
import G509.Edges9
import G509.Edges10
import G509.Edges11
import Mathlib.Tactic.IntervalCases

/-!
# G509 (Parts): a 509-vertex unit-distance graph in the plane

* `G509.unit_edges`: the 2442 edges of `edges` join points `P i`, `P j`
  at distance exactly 1 (exact check in ℤ[√3, √5, √11] by the kernel).
* `G509.plane_non_4_colorable_of`: the form of the theorem `plane_non_4_colorable` of
  vasnesterov/HadwigerNelson (G510), CONDITIONAL on the non-4-colorability of the finite combinatorial
  graph `edges` (hypothesis `hG`, a purely finite statement, proved in `G509/Final.lean`).
* `G509.P_448`: checks that point 448 is the one of Parts' file,
  with the coordinate `√(5(7+√33)/2)/8`.
-/

namespace G509

lemma all_chunks {α : Type} (l : List α) (p : α → Bool) (c : ℕ) :
    ∀ m, (∀ k < m, ((l.drop (c * k)).take c).all p = true) →
      (l.drop (c * m)).all p = true → l.all p = true := by
  intro m
  induction m with
  | zero => intro _ h; simpa using h
  | succ m ih =>
    intro hk h
    apply ih (fun k hk' => hk k (by omega))
    have e : l.drop (c * m) = (l.drop (c * m)).take c ++ (l.drop (c * m)).drop c :=
      (List.take_append_drop _ _).symm
    rw [e, List.all_append, Bool.and_eq_true]
    refine ⟨hk m (by omega), ?_⟩
    rw [List.drop_drop]
    have : c * m + c = c * (m + 1) := by ring
    rwa [this]

theorem edges_tail : (edges.drop (204 * 12)).all edgeOK = true := by decide +kernel

theorem edges_all_ok : edges.all edgeOK = true := by
  apply all_chunks edges edgeOK 204 12 _ edges_tail
  intro k hk
  interval_cases k
  · exact edges_ok_0
  · exact edges_ok_1
  · exact edges_ok_2
  · exact edges_ok_3
  · exact edges_ok_4
  · exact edges_ok_5
  · exact edges_ok_6
  · exact edges_ok_7
  · exact edges_ok_8
  · exact edges_ok_9
  · exact edges_ok_10
  · exact edges_ok_11

theorem edges_lt : edges.all (fun e => decide (e.1 < 509 ∧ e.2 < 509)) = true := by decide +kernel

/-- The 2442 edges have length exactly 1. -/
theorem unit_edges : ∀ e ∈ edges, unitDistance (P e.1) (P e.2) := by
  intro e he
  have h := List.all_eq_true.mp edges_all_ok e he
  exact Pt.norm_sub_eq_one h

/-- The finite graph `edges` (vertices `0, …, 508`) has no proper 4-coloring. -/
def NotFourColorable : Prop := ¬ ∃ c : ℕ → Fin 4, ∀ e ∈ edges, c e.1 ≠ c e.2

/-- The form of the G510 theorem `plane_non_4_colorable` of vasnesterov/HadwigerNelson, conditional on
`NotFourColorable`. -/
theorem plane_non_4_colorable_of (hG : NotFourColorable) : ¬ planeColorable 4 := by
  rintro ⟨f, hf⟩
  exact hG ⟨fun i => f (P i), fun e he => hf _ _ (unit_edges e he)⟩

/-- The set of points of G509. -/
noncomputable def S : Finset ℂ := ((List.range 509).map P).toFinset

lemma P_mem_S {i : ℕ} (hi : i < 509) : P i ∈ S := by
  simp only [S, List.mem_toFinset, List.mem_map, List.mem_range]
  exact ⟨i, hi, rfl⟩

lemma S_card_le : S.card ≤ 509 := by
  simpa [S] using List.toFinset_card_le ((List.range 509).map P)

/-- "There is a set of at most 509 points of the plane with no proper 4-coloring", conditional. -/
theorem exists_509_le_of (hG : NotFourColorable) :
    ∃ T : Finset ℂ, T.card ≤ 509 ∧
      ¬ ∃ f : ℂ → Fin 4, ∀ u ∈ T, ∀ v ∈ T, unitDistance u v → f u ≠ f v := by
  refine ⟨S, S_card_le, ?_⟩
  rintro ⟨f, hf⟩
  apply hG
  refine ⟨fun i => f (P i), fun e he => ?_⟩
  have hlt := of_decide_eq_true (List.all_eq_true.mp edges_lt e he)
  exact hf _ (P_mem_S hlt.1) _ (P_mem_S hlt.2) (unit_edges e he)

/-- The nested radical of the README: `√(5(7+√33)/2) = (√15 + √55)/2`. -/
lemma nested_radical : √(5 * (7 + √33) / 2) = (√3 * √5 + √5 * √11) / 2 := by
  have h33 : √33 = √3 * √11 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h0 : 0 ≤ (√3 * √5 + √5 * √11) / 2 := by positivity
  rw [← Real.sqrt_sq h0]
  congr 1
  rw [h33]
  linear_combination (-(1:ℝ)/4) * (√5 * √5) * sqrt3_mul
    + (-(1:ℝ)/4) * (√11 * √11 + 3 + 2 * √3 * √11) * sqrt5_mul + (-(5:ℝ)/4) * sqrt11_mul

lemma pt448 : pts.getD 448 default =
    ((((42, 0), (0, 0)), ((0, 14), (0, 0))), (((0, 0), (0, 6)), ((0, 0), (6, 0)))) := by
  decide +kernel

/-- Point 448 is `(7(3+√33)/48, √(5(7+√33)/2)/8)`, as in `509_parts.vtx` (line 449). -/
theorem P_448 : P 448 = ⟨7 * (3 + √33) / 48, √(5 * (7 + √33) / 2) / 8⟩ := by
  have h33 : √33 = √3 * √11 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [P, pt448, nested_radical, h33]
  apply Complex.ext <;> simp [Pt.toC, ev3, ev2, ev1] <;> ring

end G509

#print axioms G509.unit_edges
#print axioms G509.plane_non_4_colorable_of
#print axioms G509.exists_509_le_of
#print axioms G509.P_448
