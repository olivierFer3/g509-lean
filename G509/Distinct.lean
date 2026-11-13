/-
Copyright (c) 2026 olivierFer3. Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Main
import G509.DistinctData

/-!
# The 509 points of G509 are pairwise distinct

Real key `Kr p = 10⁹·(1000·ev3 p.1 + ev3 p.2)` (that is, `96·10⁹·(1000 x + y)`), enclosed
by exact integers `keyLo p ≤ Kr p ≤ keyHi p` thanks to `L ≤ 10⁹·√b ≤ L + 1`
(`L = ⌊10⁹√b⌋`, proved with squares of integers). The kernel checks (`decide +kernel`) that, in the order
`sigma`, `keyHi` of a point is strictly less than `keyLo` of the next one: the real keys
are strictly increasing along `sigma`, hence the points are distinct.
-/

namespace G509

lemma sqrt_enc (b : ℕ) (l : ℤ) (h0 : 0 ≤ l) (h1 : l ^ 2 ≤ 10 ^ 18 * (b : ℤ))
    (h2 : 10 ^ 18 * (b : ℤ) ≤ (l + 1) ^ 2) :
    (l : ℝ) ≤ 10 ^ 9 * √(b : ℝ) ∧ 10 ^ 9 * √(b : ℝ) ≤ (l : ℝ) + 1 := by
  have e : (10 : ℝ) ^ 9 * √(b : ℝ) = √(10 ^ 18 * (b : ℝ)) := by
    rw [Real.sqrt_mul (by positivity), show (10 : ℝ) ^ 18 = (10 ^ 9) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have h1' : ((l : ℝ)) ^ 2 ≤ 10 ^ 18 * (b : ℝ) := by exact_mod_cast h1
  have h2' : 10 ^ 18 * (b : ℝ) ≤ ((l : ℝ) + 1) ^ 2 := by exact_mod_cast h2
  have hl : (0 : ℝ) ≤ l := by exact_mod_cast h0
  rw [e]
  constructor
  · calc (l : ℝ) = √((l : ℝ) ^ 2) := (Real.sqrt_sq hl).symm
      _ ≤ _ := Real.sqrt_le_sqrt h1'
  · calc √(10 ^ 18 * (b : ℝ)) ≤ √(((l : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt h2'
      _ = (l : ℝ) + 1 := Real.sqrt_sq (by linarith)

/-- Lower bound of a term `c·t` when `l ≤ t ≤ l + 1`. -/
def tlo (c l : ℤ) : ℤ := if 0 ≤ c then c * l else c * (l + 1)
def thi (c l : ℤ) : ℤ := if 0 ≤ c then c * (l + 1) else c * l

lemma term_enc (c l : ℤ) (t : ℝ) (h : (l : ℝ) ≤ t ∧ t ≤ (l : ℝ) + 1) :
    (tlo c l : ℝ) ≤ c * t ∧ c * t ≤ (thi c l : ℝ) := by
  obtain ⟨h1, h2⟩ := h
  unfold tlo thi
  split_ifs with hc
  · have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
    push_cast; constructor <;> nlinarith
  · have hc' : (c : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hc)
    push_cast; constructor <;> nlinarith

def L1 : ℤ := 1732050807
def L2 : ℤ := 2236067977
def L3 : ℤ := 3872983346
def L4 : ℤ := 3316624790
def L5 : ℤ := 5744562646
def L6 : ℤ := 7416198487
def L7 : ℤ := 12845232578


def lo3 (x : Q3) : ℤ :=
  x.1.1.1 * 1000000000 + tlo x.1.1.2 L1 + tlo x.1.2.1 L2 + tlo x.1.2.2 L3 +
  tlo x.2.1.1 L4 + tlo x.2.1.2 L5 + tlo x.2.2.1 L6 + tlo x.2.2.2 L7
def hi3 (x : Q3) : ℤ :=
  x.1.1.1 * 1000000000 + thi x.1.1.2 L1 + thi x.1.2.1 L2 + thi x.1.2.2 L3 +
  thi x.2.1.1 L4 + thi x.2.1.2 L5 + thi x.2.2.1 L6 + thi x.2.2.2 L7

lemma ev3_flat (x : Q3) : ev3 x =
    x.1.1.1 + x.1.1.2 * √3 + x.1.2.1 * √5 + x.1.2.2 * √15 + x.2.1.1 * √11 +
    x.2.1.2 * √33 + x.2.2.1 * √55 + x.2.2.2 * √165 := by
  have h15 : √15 = √3 * √5 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h33 : √33 = √3 * √11 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h55 : √55 = √5 * √11 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h165 : √165 = √3 * √5 * √11 := by
    rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by norm_num)]; norm_num
  rw [h15, h33, h55, h165]
  simp only [ev3, ev2, ev1]
  ring

lemma enc3 (x : Q3) : (lo3 x : ℝ) ≤ 10 ^ 9 * ev3 x ∧ 10 ^ 9 * ev3 x ≤ (hi3 x : ℝ) := by
  have t1 := term_enc x.1.1.2 L1 _ (sqrt_enc 3 L1 (by norm_num [L1]) (by norm_num [L1]) (by norm_num [L1]))
  have t2 := term_enc x.1.2.1 L2 _ (sqrt_enc 5 L2 (by norm_num [L2]) (by norm_num [L2]) (by norm_num [L2]))
  have t3 := term_enc x.1.2.2 L3 _ (sqrt_enc 15 L3 (by norm_num [L3]) (by norm_num [L3]) (by norm_num [L3]))
  have t4 := term_enc x.2.1.1 L4 _ (sqrt_enc 11 L4 (by norm_num [L4]) (by norm_num [L4]) (by norm_num [L4]))
  have t5 := term_enc x.2.1.2 L5 _ (sqrt_enc 33 L5 (by norm_num [L5]) (by norm_num [L5]) (by norm_num [L5]))
  have t6 := term_enc x.2.2.1 L6 _ (sqrt_enc 55 L6 (by norm_num [L6]) (by norm_num [L6]) (by norm_num [L6]))
  have t7 := term_enc x.2.2.2 L7 _ (sqrt_enc 165 L7 (by norm_num [L7]) (by norm_num [L7]) (by norm_num [L7]))
  simp only [Nat.cast_ofNat] at t1 t2 t3 t4 t5 t6 t7
  rw [ev3_flat]
  simp only [lo3, hi3]
  push_cast
  constructor <;> nlinarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2, t5.1, t5.2,
    t6.1, t6.2, t7.1, t7.2]

def keyLo (p : Pt) : ℤ := 1000 * lo3 p.1 + lo3 p.2
def keyHi (p : Pt) : ℤ := 1000 * hi3 p.1 + hi3 p.2

/-- Real key, as a function of the complex point `P i`. -/
noncomputable def Kc (z : ℂ) : ℝ := 10 ^ 9 * (1000 * (96 * z.re) + 96 * z.im)

lemma key_enc (p : Pt) : (keyLo p : ℝ) < Kc p.toC + 1 ∧ Kc p.toC ≤ (keyHi p : ℝ) := by
  have a := enc3 p.1
  have b := enc3 p.2
  have hK : Kc p.toC = 1000 * (10 ^ 9 * ev3 p.1) + 10 ^ 9 * ev3 p.2 := by
    simp only [Kc, Pt.toC]; ring
  rw [hK]; simp only [keyLo, keyHi]; push_cast
  constructor <;> linarith [a.1, a.2, b.1, b.2]

def chainOK : List ℕ → Bool
  | a :: b :: t => decide (keyHi (pts.getD a default) < keyLo (pts.getD b default)) && chainOK (b :: t)
  | _ => true

theorem chainOK_sigma : chainOK sigma = true := by decide +kernel
theorem sigma_length : sigma.length = 509 := by decide +kernel
theorem sigma_lt : sigma.all (fun i => decide (i < 509)) = true := by decide +kernel

lemma chain_pairwise : ∀ l : List ℕ, chainOK l = true → l.Pairwise (fun a b => Kc (P a) < Kc (P b))
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := chain_pairwise (b :: t) h.2
    have hab : Kc (P a) < Kc (P b) := by
      have ka := key_enc (pts.getD a default)
      have kb := key_enc (pts.getD b default)
      have hz : (keyHi (pts.getD a default) : ℝ) + 1 ≤ keyLo (pts.getD b default) := by
        exact_mod_cast h.1
      simp only [P]; linarith [ka.2, kb.1]
    refine List.pairwise_cons.mpr ⟨?_, ih⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hab
    · exact lt_trans hab ((List.pairwise_cons.mp ih).1 c hc)

theorem S_card : S.card = 509 := by
  have hp := chain_pairwise sigma chainOK_sigma
  have hnd : (sigma.map P).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact hp.imp (fun h e => (ne_of_lt h) (congrArg Kc e))
  have hsub : (sigma.map P).toFinset ⊆ S := by
    intro z hz
    simp only [List.mem_toFinset, List.mem_map] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    exact P_mem_S (of_decide_eq_true (List.all_eq_true.mp sigma_lt i hi))
  have hc : (sigma.map P).toFinset.card = 509 := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map, sigma_length]
  have := Finset.card_le_card hsub
  have := S_card_le
  omega

/-- "There is a set of 509 points of the plane with no proper 4-coloring", conditional on `hG`. -/
theorem exists_509_of (hG : NotFourColorable) :
    ∃ T : Finset ℂ, T.card = 509 ∧
      ¬ ∃ f : ℂ → Fin 4, ∀ u ∈ T, ∀ v ∈ T, unitDistance u v → f u ≠ f v := by
  refine ⟨S, S_card, ?_⟩
  rintro ⟨f, hf⟩
  apply hG
  refine ⟨fun i => f (P i), fun e he => ?_⟩
  have hlt := of_decide_eq_true (List.all_eq_true.mp edges_lt e he)
  exact hf _ (P_mem_S hlt.1) _ (P_mem_S hlt.2) (unit_edges e he)

end G509

#print axioms G509.S_card
#print axioms G509.exists_509_of
