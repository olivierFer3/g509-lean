/-
Copyright (c) 2026 olivierFer3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Main
import G509.CNF
import Mathlib.Tactic.FinCases

/-!
# From SAT to colorings

`G509.notFour_of_unsat`: if the CNF `G509C.F` (4-coloring of `edges`, triangle 0, 149, 152
colored 0, 1, 2) is unsatisfiable, then `NotFourColorable`. The symmetry breaking is
justified by a permutation of the colors.
-/

namespace G509

theorem edgeCode_eq : G509C.edgeCode = edges.map (fun e => e.1 * 1024 + e.2) := by decide +kernel

theorem tri : (0, 149) ∈ edges ∧ (0, 152) ∈ edges ∧ (149, 152) ∈ edges := by decide +kernel

/-- Permutation of the colors sending `a, b, d` to `0, 1, 2`. -/
def sig (a b d x : Fin 4) : Fin 4 := if x = a then 0 else if x = b then 1 else if x = d then 2 else 3

theorem sig_inj : ∀ a b d x y : Fin 4, a ≠ b → a ≠ d → b ≠ d → sig a b d x = sig a b d y → x = y := by
  decide

theorem litpos (τ : Nat → Bool) (x : Nat) : LR.litT τ (G509C.posL x) = τ x := by
  unfold LR.litT G509C.posL
  have h1 : 2 * x % 2 = 0 := by omega
  have h2 : 2 * x / 2 = x := by omega
  simp [h1, h2]

theorem litneg (τ : Nat → Bool) (x : Nat) : LR.litT τ (G509C.negL x) = !τ x := by
  unfold LR.litT G509C.negL
  have h1 : (2 * x + 1) % 2 = 1 := by omega
  have h2 : (2 * x + 1) / 2 = x := by omega
  simp [h1, h2]

theorem alo_ok (v : Nat) : ∀ z : Fin 4, ∀ τ : Nat → Bool,
    (∀ k < 4, τ (G509C.var v k) = decide (z.val = k)) →
    LR.clauseT τ [G509C.posL (G509C.var v 0), G509C.posL (G509C.var v 1),
      G509C.posL (G509C.var v 2), G509C.posL (G509C.var v 3)] = true := by
  intro z τ hτ
  have e0 := hτ 0 (by omega); have e1 := hτ 1 (by omega)
  have e2 := hτ 2 (by omega); have e3 := hτ 3 (by omega)
  simp only [LR.clauseT, List.any_cons, List.any_nil, litpos, e0, e1, e2, e3]
  fin_cases z <;> simp

theorem notFour_of_unsat (h : ∀ τ, ¬ LR.SatF τ G509C.F) : NotFourColorable := by
  rintro ⟨c, hc⟩
  obtain ⟨h1, h2, h3⟩ := tri
  have hab : c 0 ≠ c 149 := hc _ h1
  have had : c 0 ≠ c 152 := hc _ h2
  have hbd : c 149 ≠ c 152 := hc _ h3
  let c' : ℕ → Fin 4 := fun v => sig (c 0) (c 149) (c 152) (c v)
  have hc' : ∀ e ∈ edges, c' e.1 ≠ c' e.2 := fun e he heq =>
    hc e he (sig_inj _ _ _ _ _ hab had hbd heq)
  let τ : Nat → Bool := fun x => decide ((c' ((x - 1) / 4)).val = (x - 1) % 4)
  have tv : ∀ v k, k < 4 → τ (G509C.var v k) = decide ((c' v).val = k) := by
    intro v k hk
    have a1 : (G509C.var v k - 1) / 4 = v := by unfold G509C.var; omega
    have a2 : (G509C.var v k - 1) % 4 = k := by unfold G509C.var; omega
    simp only [τ, a1, a2]
  apply h τ
  intro cl hcl
  simp only [G509C.F, List.mem_append] at hcl
  rcases hcl with (hcl | hcl) | hcl
  · simp only [G509C.alo, List.mem_map, List.mem_range] at hcl
    obtain ⟨v, -, rfl⟩ := hcl
    exact alo_ok v (c' v) τ (fun k hk => tv v k hk)
  · simp only [G509C.edgeCl, List.mem_flatMap, List.mem_map] at hcl
    obtain ⟨e, he, k, hk, rfl⟩ := hcl
    rw [edgeCode_eq, List.mem_map] at he
    obtain ⟨⟨u, w⟩, huw, he'⟩ := he
    simp only at he'
    subst he'
    have hlt := of_decide_eq_true (List.all_eq_true.mp edges_lt _ huw)
    simp only at hlt
    have q1 : (u * 1024 + w) / 1024 = u := by omega
    have q2 : (u * 1024 + w) % 1024 = w := by omega
    have hk4 : k < 4 := by simp at hk; omega
    have hne : (c' u).val ≠ (c' w).val := fun e => hc' _ huw (Fin.ext e)
    simp only [LR.clauseT, List.any_cons, List.any_nil, litneg, q1, q2, tv u k hk4, tv w k hk4]
    by_cases hu : (c' u).val = k <;> by_cases hw : (c' w).val = k <;> simp [hu, hw] <;> omega
  · have s0 : (c' 0).val = 0 := by simp [c', sig]
    have s1 : (c' 149).val = 1 := by simp [c', sig, Ne.symm hab]
    have s2 : (c' 152).val = 2 := by simp [c', sig, Ne.symm had, Ne.symm hbd]
    simp only [G509C.units, List.mem_cons, List.mem_nil_iff, or_false] at hcl
    rcases hcl with rfl | rfl | rfl <;>
      simp [LR.clauseT, litpos, tv 0 0 (by omega), tv 149 1 (by omega), tv 152 2 (by omega),
        s0, s1, s2]

end G509

#print axioms G509.notFour_of_unsat
