/-
Copyright (c) 2026 olivierFer3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Exact arithmetic in ℤ[√3, √5, √11]

Tower of quadratic extensions: `Q1 = ℤ[√3]`, `Q2 = Q1[√5]`, `Q3 = Q2[√11]`, each level
represented by a pair `(x, y) ↦ x + y·√d`. The operations are explicit functions
on `ℤ` that the kernel can reduce (`decide +kernel`). The functions `ev1`, `ev2`, `ev3`
send a representation to the corresponding real number; the lemmas `ev*_add/sub/mul` say that
they are homomorphisms. No linear independence assumption is needed.
-/

namespace G509

abbrev Q1 := ℤ × ℤ
abbrev Q2 := Q1 × Q1
abbrev Q3 := Q2 × Q2

def Q1.add (x y : Q1) : Q1 := (x.1 + y.1, x.2 + y.2)
def Q1.sub (x y : Q1) : Q1 := (x.1 - y.1, x.2 - y.2)
def Q1.smul (k : ℤ) (x : Q1) : Q1 := (k * x.1, k * x.2)
def Q1.mul (x y : Q1) : Q1 := (x.1 * y.1 + 3 * (x.2 * y.2), x.1 * y.2 + x.2 * y.1)

def Q2.add (x y : Q2) : Q2 := (Q1.add x.1 y.1, Q1.add x.2 y.2)
def Q2.sub (x y : Q2) : Q2 := (Q1.sub x.1 y.1, Q1.sub x.2 y.2)
def Q2.smul (k : ℤ) (x : Q2) : Q2 := (Q1.smul k x.1, Q1.smul k x.2)
def Q2.mul (x y : Q2) : Q2 :=
  (Q1.add (Q1.mul x.1 y.1) (Q1.smul 5 (Q1.mul x.2 y.2)), Q1.add (Q1.mul x.1 y.2) (Q1.mul x.2 y.1))

def Q3.add (x y : Q3) : Q3 := (Q2.add x.1 y.1, Q2.add x.2 y.2)
def Q3.sub (x y : Q3) : Q3 := (Q2.sub x.1 y.1, Q2.sub x.2 y.2)
def Q3.mul (x y : Q3) : Q3 :=
  (Q2.add (Q2.mul x.1 y.1) (Q2.smul 11 (Q2.mul x.2 y.2)), Q2.add (Q2.mul x.1 y.2) (Q2.mul x.2 y.1))

noncomputable def ev1 (x : Q1) : ℝ := (x.1 : ℝ) + (x.2 : ℝ) * √3
noncomputable def ev2 (x : Q2) : ℝ := ev1 x.1 + ev1 x.2 * √5
noncomputable def ev3 (x : Q3) : ℝ := ev2 x.1 + ev2 x.2 * √11

lemma sqrt3_mul : √3 * √3 = (3 : ℝ) := Real.mul_self_sqrt (by norm_num)
lemma sqrt5_mul : √5 * √5 = (5 : ℝ) := Real.mul_self_sqrt (by norm_num)
lemma sqrt11_mul : √11 * √11 = (11 : ℝ) := Real.mul_self_sqrt (by norm_num)

lemma ev1_add (x y : Q1) : ev1 (Q1.add x y) = ev1 x + ev1 y := by
  simp only [ev1, Q1.add]; push_cast; ring
lemma ev1_sub (x y : Q1) : ev1 (Q1.sub x y) = ev1 x - ev1 y := by
  simp only [ev1, Q1.sub]; push_cast; ring
lemma ev1_smul (k : ℤ) (x : Q1) : ev1 (Q1.smul k x) = k * ev1 x := by
  simp only [ev1, Q1.smul]; push_cast; ring
lemma ev1_mul (x y : Q1) : ev1 (Q1.mul x y) = ev1 x * ev1 y := by
  simp only [ev1, Q1.mul]; push_cast
  linear_combination (-(x.2 : ℝ) * y.2) * sqrt3_mul

lemma ev2_add (x y : Q2) : ev2 (Q2.add x y) = ev2 x + ev2 y := by
  simp only [ev2, Q2.add, ev1_add]; ring
lemma ev2_sub (x y : Q2) : ev2 (Q2.sub x y) = ev2 x - ev2 y := by
  simp only [ev2, Q2.sub, ev1_sub]; ring
lemma ev2_smul (k : ℤ) (x : Q2) : ev2 (Q2.smul k x) = k * ev2 x := by
  simp only [ev2, Q2.smul, ev1_smul]; ring
lemma ev2_mul (x y : Q2) : ev2 (Q2.mul x y) = ev2 x * ev2 y := by
  simp only [ev2, Q2.mul, ev1_add, ev1_mul, ev1_smul]; push_cast
  linear_combination (-(ev1 x.2) * ev1 y.2) * sqrt5_mul

lemma ev3_add (x y : Q3) : ev3 (Q3.add x y) = ev3 x + ev3 y := by
  simp only [ev3, Q3.add, ev2_add]; ring
lemma ev3_sub (x y : Q3) : ev3 (Q3.sub x y) = ev3 x - ev3 y := by
  simp only [ev3, Q3.sub, ev2_sub]; ring
lemma ev3_mul (x y : Q3) : ev3 (Q3.mul x y) = ev3 x * ev3 y := by
  simp only [ev3, Q3.mul, ev2_add, ev2_mul, ev2_smul]; push_cast
  linear_combination (-(ev2 x.2) * ev2 y.2) * sqrt11_mul

/-- The integer `k` seen in `Q3`. -/
def Q3.ofInt (k : ℤ) : Q3 := (((k, 0), (0, 0)), ((0, 0), (0, 0)))

lemma ev3_ofInt (k : ℤ) : ev3 (Q3.ofInt k) = k := by
  simp [ev3, ev2, ev1, Q3.ofInt]

/-- A point of the plane, coordinates multiplied by `96`. -/
abbrev Pt := Q3 × Q3

noncomputable def Pt.toC (p : Pt) : ℂ := ⟨ev3 p.1 / 96, ev3 p.2 / 96⟩

/-- Squared distance (times `96²`), computed exactly. -/
def Pt.dist2 (p q : Pt) : Q3 :=
  Q3.add (Q3.mul (Q3.sub p.1 q.1) (Q3.sub p.1 q.1)) (Q3.mul (Q3.sub p.2 q.2) (Q3.sub p.2 q.2))

/-- Boolean test "unit distance". -/
def Pt.isUnit (p q : Pt) : Bool := decide (Pt.dist2 p q = Q3.ofInt 9216)

theorem Pt.norm_sub_eq_one {p q : Pt} (h : Pt.isUnit p q = true) : ‖p.toC - q.toC‖ = 1 := by
  have h' : Pt.dist2 p q = Q3.ofInt 9216 := of_decide_eq_true h
  have hr : (ev3 p.1 - ev3 q.1) ^ 2 + (ev3 p.2 - ev3 q.2) ^ 2 = 9216 := by
    have := congrArg ev3 h'
    simp only [Pt.dist2, ev3_add, ev3_mul, ev3_sub, ev3_ofInt] at this
    push_cast at this
    linear_combination this
  have hn : Complex.normSq (p.toC - q.toC) = 1 := by
    rw [Complex.normSq_apply]
    simp only [Pt.toC, Complex.sub_re, Complex.sub_im]
    linear_combination hr / 9216
  have : ‖p.toC - q.toC‖ ^ 2 = 1 := by rw [Complex.sq_norm, hn]
  have h0 : 0 ≤ ‖p.toC - q.toC‖ := norm_nonneg _
  nlinarith

end G509
