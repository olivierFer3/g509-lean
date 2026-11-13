/-
Copyright (c) 2026 olivierFer3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.RUP
import G509.Test.RMoser.FT

namespace G509.Test.RMoser
open RV RV.Tb

set_option maxRecDepth 100000 in
def t0 : Tb :=
  nd (nd (nd (nd (nd (nd (lf [7, 19]) (lf [19, 25])) (nd (lf [32, 34, 36]) (lf [22, 5]))) (nd (nd (lf [11, 23]) (lf [21, 7])) (nd (lf [3, 33]) (lf [35])))) (nd (nd (nd (lf [8, 10, 12]) (lf [27, 39])) (nd (lf [13, 19]) (lf [37]))) (nd (nd (lf [31, 43]) (lf [43])) (lf [31, 37])))) (nd (nd (nd (nd (lf [9, 21]) (lf [5, 11])) (nd (lf [3, 15]) (lf [6]))) (nd (nd (lf [9, 15]) (lf [5, 43])) (nd (lf [29, 41]) (lf [32])))) (nd (nd (nd (lf [11, 17]) (lf [7, 31])) (nd (lf [2, 4, 6]) (lf [40]))) (nd (nd (lf [5, 35]) (lf [3])) (lf [21, 39]))))) (nd (nd (nd (nd (nd (lf [7, 13]) (lf [5, 17])) (nd (lf [27, 33]) (lf [5]))) (nd (nd (lf [17, 23]) (lf [7, 24])) (nd (lf [29, 35]) (lf [26])))) (nd (nd (nd (lf [14, 16, 18]) (lf [33, 39])) (nd (lf [25, 43]) (lf [39]))) (nd (nd (lf [5, 29]) (lf [41, 3])) (lf [38, 40, 42])))) (nd (nd (nd (nd (lf [15, 21]) (lf [23, 41])) (nd (lf [3, 9]) (lf [31]))) (nd (nd (lf [37, 43]) (lf [23, 3])) (nd (lf [35, 41]) (lf [])))) (nd (nd (nd (lf [20, 22, 24]) (lf [7, 37])) (nd (lf [3, 27]) (lf [29]))) (nd (nd (lf [26, 28, 30]) (lf [15, 22, 10])) (lf [13, 25])))))

def fs0 : List Nat := [12, 9, 16, 19, 1, 2, 14, 3, 17, 20, 13, 36, 33, 23, 26, 4, 5, 28, 10, 7, 15, 39, 0, 22, 25, 29, 32, 35, 30, 6, 37, 18, 21, 11, 8, 38, 31, 34, 24, 27]

set_option maxRecDepth 100000 in
def hs0 : List (List Nat) := [
  [0, 1, 2, 3, 4, 5, 6],
  [1, 0, 40, 7, 8, 9, 4, 5, 10],
  [11, 12, 13, 14, 15, 16, 17],
  [18, 19, 8, 9, 4, 5, 20],
  [12, 11, 21, 41, 42, 22, 23, 24, 15, 16, 25],
  [24, 23, 26, 27, 15, 16, 28],
  [44, 19, 18, 43, 45, 29, 30, 7, 31, 32, 4, 5, 6],
  [10, 3, 4, 7, 31],
  [33, 34, 47, 5, 20, 32, 4, 7, 2],
  [44, 13, 14, 48, 35, 29, 36, 37, 15, 16, 28],
  [49, 46, 22],
  [50, 38],
  [50, 39],
  [51, 52, 36, 37, 15, 16, 25],
  [53, 44, 29],
  [54, 26],
  [54, 27],
  [55, 51, 15],
  [56, 52, 16],
  [57, 58, 17]]

set_option maxRecDepth 100000 in
def es0 : List (Nat × List Nat) := [
  (59, [])]

theorem ok0 : chunkCheck FT 40 t0 fs0 (snds ([] : List (Nat × List Nat))) hs0 es0 = true := by decide +kernel

theorem inv0 (τ : Nat → Bool) (hF : LR.SatF τ F) : ∀ p ∈ es0, LR.clauseT τ p.2 = true :=
  chunk_step FT 40 t0 fs0 ([] : List (Nat × List Nat)) hs0 es0 ok0 τ (FT_good τ hF) (by simp)

theorem unsat : ∀ τ, ¬ LR.SatF τ F := fun τ hF =>
  not_empty τ es0 59 (by simp [es0]) (inv0 τ hF)

end G509.Test.RMoser

#print axioms G509.Test.RMoser.unsat
