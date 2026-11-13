/-
Copyright (c) 2026 olivierFer3. Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.RUP

namespace G509.Test.RMoser
open RV RV.Tb

def F : List (List Nat) := [
  [2, 4, 6],
  [8, 10, 12],
  [14, 16, 18],
  [20, 22, 24],
  [26, 28, 30],
  [32, 34, 36],
  [38, 40, 42],
  [3, 9],
  [5, 11],
  [7, 13],
  [3, 15],
  [5, 17],
  [7, 19],
  [9, 15],
  [11, 17],
  [13, 19],
  [9, 21],
  [11, 23],
  [13, 25],
  [15, 21],
  [17, 23],
  [19, 25],
  [3, 27],
  [5, 29],
  [7, 31],
  [3, 33],
  [5, 35],
  [7, 37],
  [27, 33],
  [29, 35],
  [31, 37],
  [27, 39],
  [29, 41],
  [31, 43],
  [33, 39],
  [35, 41],
  [37, 43],
  [21, 39],
  [23, 41],
  [25, 43]]

set_option maxRecDepth 100000 in
def FT : Tb :=
  nd (nd (nd (nd (nd (nd (lf [2, 4, 6]) (lf [29, 41])) (lf [9, 21])) (nd (lf [5, 11]) (lf [7, 31]))) (nd (nd (nd (lf [26, 28, 30]) (lf [37, 43])) (lf [17, 23])) (nd (lf [7, 19]) (lf [27, 33])))) (nd (nd (nd (nd (lf [14, 16, 18]) (lf [33, 39])) (lf [13, 25])) (nd (lf [3, 15]) (lf [5, 35]))) (nd (nd (nd (lf [38, 40, 42]) (lf [23, 41])) (lf [3, 27])) (nd (lf [11, 17]) (lf [31, 37]))))) (nd (nd (nd (nd (nd (lf [8, 10, 12]) (lf [31, 43])) (lf [11, 23])) (nd (lf [7, 13]) (lf [3, 33]))) (nd (nd (nd (lf [32, 34, 36]) (lf [21, 39])) (lf [19, 25])) (nd (lf [9, 15]) (lf [29, 35])))) (nd (nd (nd (nd (lf [20, 22, 24]) (lf [35, 41])) (lf [15, 21])) (nd (lf [5, 17]) (lf [7, 37]))) (nd (nd (nd (lf [3, 9]) (lf [25, 43])) (lf [5, 29])) (nd (lf [13, 19]) (lf [27, 39])))))

theorem FT_ok : baseOK FT F 0 = true := by decide +kernel

theorem len_F : len F = 40 := by decide +kernel

theorem FT_good (τ : Nat → Bool) (h : LR.SatF τ F) : Good τ FT 40 := by
  have := ft_good FT F FT_ok τ h; rwa [len_F] at this

end G509.Test.RMoser
