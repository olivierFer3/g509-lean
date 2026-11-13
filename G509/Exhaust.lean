/-
Copyright (c) 2026 olivierFer3. Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Distinct
import G509.ExhaustData

/-!
# Exhaustiveness of the edges of G509: definitions and soundness

For each point `p`, `boxOf p = (lo3 p.1, hi3 p.1, lo3 p.2, hi3 p.2)` encloses `10⁹·96·(x, y)`
(`enc3`, `G509/Distinct.lean`). For a pair `(i, j)`, `far` checks, in integers, that the interval
of `10¹⁸·96²·‖P i − P j‖²` does not contain `9216·10¹⁸`; then `‖P i − P j‖ ≠ 1` (`far_sound`).
`rowOK` scans a row `i`: each `j > i` is either in the adjacency list `adjN[i]`, or
separated by `far`. The functions are written with the recursors (`List.rec`) for kernel
reduction, as in `G509/RUP.lean`. The chunks `G509/X/R*.lean` check the rows by
`decide +kernel`. Final result: `G509/ExhaustFinal.lean`.
-/

namespace G509.EX

abbrev Box := ℤ × ℤ × ℤ × ℤ

def boxOf (p : Pt) : Box := (lo3 p.1, hi3 p.1, lo3 p.2, hi3 p.2)

def OFF : ℤ := 1099511627776

def dec (c : ℕ × ℕ × ℕ × ℕ) : Box :=
  ((c.1 : ℤ) - OFF, (c.2.1 : ℤ) - OFF, (c.2.2.1 : ℤ) - OFF, (c.2.2.2 : ℤ) - OFF)

def boxes : List Box := boxesN.map dec

theorem boxes_eq : boxes = pts.map boxOf := by decide +kernel

def TT : ℤ := 9216 * 10 ^ 18

def sqmax (l h : ℤ) : ℤ := max (l * l) (h * h)
def sqmin (l h : ℤ) : ℤ := if 0 < l then l * l else if h < 0 then h * h else 0

def far (a b : Box) : Bool :=
  decide (sqmax (a.1 - b.2.1) (a.2.1 - b.1) + sqmax (a.2.2.1 - b.2.2.2) (a.2.2.2 - b.2.2.1) < TT) ||
  decide (TT < sqmin (a.1 - b.2.1) (a.2.1 - b.1) + sqmin (a.2.2.1 - b.2.2.2) (a.2.2.2 - b.2.2.1))

lemma sq_le_sqmax {l h : ℤ} {t : ℝ} (h1 : (l : ℝ) ≤ t) (h2 : t ≤ (h : ℝ)) :
    t * t ≤ ((sqmax l h : ℤ) : ℝ) := by
  unfold sqmax
  push_cast
  rcases le_total 0 t with ht | ht
  · exact le_trans (by nlinarith) (le_max_right _ _)
  · exact le_trans (by nlinarith) (le_max_left _ _)

lemma sqmin_le_sq {l h : ℤ} {t : ℝ} (h1 : (l : ℝ) ≤ t) (h2 : t ≤ (h : ℝ)) :
    ((sqmin l h : ℤ) : ℝ) ≤ t * t := by
  unfold sqmin
  split_ifs with ha hb
  · have : (0 : ℝ) < l := by exact_mod_cast ha
    push_cast; nlinarith
  · have : (h : ℝ) < 0 := by exact_mod_cast hb
    push_cast; nlinarith
  · push_cast; nlinarith

theorem far_sound (p q : Pt) (hf : far (boxOf p) (boxOf q) = true) : ‖p.toC - q.toC‖ ≠ 1 := by
  intro hn
  have hs : Complex.normSq (p.toC - q.toC) = 1 := by
    rw [← Complex.sq_norm, hn]; norm_num
  rw [Complex.normSq_apply] at hs
  simp only [Pt.toC, Complex.sub_re, Complex.sub_im] at hs
  have a1 := enc3 p.1
  have a2 := enc3 p.2
  have b1 := enc3 q.1
  have b2 := enc3 q.2
  set X : ℝ := 10 ^ 9 * ev3 p.1 - 10 ^ 9 * ev3 q.1 with hX
  set Y : ℝ := 10 ^ 9 * ev3 p.2 - 10 ^ 9 * ev3 q.2 with hY
  have hXY : X * X + Y * Y = (TT : ℝ) := by
    simp only [TT, hX, hY]; push_cast
    have : (ev3 p.1 - ev3 q.1) * (ev3 p.1 - ev3 q.1) + (ev3 p.2 - ev3 q.2) * (ev3 p.2 - ev3 q.2)
        = 9216 := by
      have e : (ev3 p.1 / 96 - ev3 q.1 / 96) * (ev3 p.1 / 96 - ev3 q.1 / 96) +
          (ev3 p.2 / 96 - ev3 q.2 / 96) * (ev3 p.2 / 96 - ev3 q.2 / 96) = 1 := hs
      linear_combination 9216 * e
    linear_combination 10 ^ 18 * this
  have hx1 : ((lo3 p.1 - hi3 q.1 : ℤ) : ℝ) ≤ X := by push_cast; linarith [a1.1, b1.2]
  have hx2 : X ≤ ((hi3 p.1 - lo3 q.1 : ℤ) : ℝ) := by push_cast; linarith [a1.2, b1.1]
  have hy1 : ((lo3 p.2 - hi3 q.2 : ℤ) : ℝ) ≤ Y := by push_cast; linarith [a2.1, b2.2]
  have hy2 : Y ≤ ((hi3 p.2 - lo3 q.2 : ℤ) : ℝ) := by push_cast; linarith [a2.2, b2.1]
  have u1 := sq_le_sqmax hx1 hx2
  have u2 := sq_le_sqmax hy1 hy2
  have v1 := sqmin_le_sq hx1 hx2
  have v2 := sqmin_le_sq hy1 hy2
  simp only [far, boxOf, Bool.or_eq_true] at hf
  rcases hf with h | h
  · have h' : ((sqmax (lo3 p.1 - hi3 q.1) (hi3 p.1 - lo3 q.1) +
        sqmax (lo3 p.2 - hi3 q.2) (hi3 p.2 - lo3 q.2) : ℤ) : ℝ) < (TT : ℝ) := by exact_mod_cast (of_decide_eq_true h)
    push_cast at h'
    linarith
  · have h' : (TT : ℝ) < ((sqmin (lo3 p.1 - hi3 q.1) (hi3 p.1 - lo3 q.1) +
        sqmin (lo3 p.2 - hi3 q.2) (hi3 p.2 - lo3 q.2) : ℤ) : ℝ) := by exact_mod_cast (of_decide_eq_true h)
    push_cast at h'
    linarith

/-- Row: `a` = box of point `i`, `bs` = boxes of the points `j, j+1, …`, `adj` = remaining
neighbours of `i` (increasing). -/
noncomputable def rowOK (a : Box) (bs : List Box) : ℕ → List ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → List ℕ → Bool) (fun _ _ => true)
    (fun b _ ih j adj =>
      List.rec (motive := fun _ => Bool) (far a b && ih (j + 1) [])
        (fun k ks _ => (Nat.beq k j && ih (j + 1) ks) || (far a b && ih (j + 1) (k :: ks))) adj) bs

theorem rowOK_cons_nil (a b : Box) (bs : List Box) (j : ℕ) :
    rowOK a (b :: bs) j [] = (far a b && rowOK a bs (j + 1) []) := rfl

theorem rowOK_cons_cons (a b : Box) (bs : List Box) (j k : ℕ) (ks : List ℕ) :
    rowOK a (b :: bs) j (k :: ks) =
      ((Nat.beq k j && rowOK a bs (j + 1) ks) || (far a b && rowOK a bs (j + 1) (k :: ks))) := rfl

theorem rowOK_sound (a : Box) : ∀ (bs : List Box) (j : ℕ) (adj : List ℕ), rowOK a bs j adj = true →
    ∀ m, m < bs.length → (j + m) ∈ adj ∨ far a (bs.getD m (0, 0, 0, 0)) = true := by
  intro bs
  induction bs with
  | nil => intro j adj _ m hm; simp at hm
  | cons b bs ih =>
    intro j adj h m hm
    cases adj with
    | nil =>
      rw [rowOK_cons_nil, Bool.and_eq_true] at h
      cases m with
      | zero => right; simpa using h.1
      | succ m =>
        have := ih (j + 1) [] h.2 m (by simpa using hm)
        rcases this with h3 | h3
        · simp at h3
        · right; simpa using h3
    | cons k ks =>
      rw [rowOK_cons_cons, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨hk, hr⟩ | ⟨hf, hr⟩
      · have hkj : k = j := Nat.eq_of_beq_eq_true hk
        cases m with
        | zero => left; simp [hkj]
        | succ m =>
          rcases ih (j + 1) ks hr m (by simpa using hm) with h3 | h3
          · left; apply List.mem_cons_of_mem; rw [show j + (m + 1) = j + 1 + m by omega]; exact h3
          · right; simpa using h3
      · cases m with
        | zero => right; simpa using hf
        | succ m =>
          rcases ih (j + 1) (k :: ks) hr m (by simpa using hm) with h3 | h3
          · left; rw [show j + (m + 1) = j + 1 + m by omega]; exact h3
          · right; simpa using h3

/-- `n` consecutive rows, starting at row `i`: `bs` = boxes of the points `i, i+1, …`. -/
noncomputable def rowsOK (bs : List Box) : ℕ → List (List ℕ) → ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → List (List ℕ) → ℕ → Bool) (fun _ _ _ => true)
    (fun a as ih i adjs n =>
      Nat.rec (motive := fun _ => Bool) true
        (fun n' _ => rowOK a as (i + 1) (adjs.headD []) && ih (i + 1) adjs.tail n') n) bs

theorem rowsOK_cons_succ (a : Box) (as : List Box) (i : ℕ) (adjs : List (List ℕ)) (n : ℕ) :
    rowsOK (a :: as) i adjs (n + 1) = (rowOK a as (i + 1) (adjs.headD []) && rowsOK as (i + 1) adjs.tail n) :=
  rfl

theorem rowsOK_sound : ∀ (bs : List Box) (i : ℕ) (adjs : List (List ℕ)) (n : ℕ), rowsOK bs i adjs n = true →
    ∀ p, p < n → p < bs.length →
      rowOK (bs.getD p (0, 0, 0, 0)) (bs.drop (p + 1)) (i + p + 1) (adjs.getD p []) = true := by
  intro bs
  induction bs with
  | nil => intro i adjs n _ p _ hp; simp at hp
  | cons a as ih =>
    intro i adjs n h p hpn hp
    cases n with
    | zero => omega
    | succ n =>
      rw [rowsOK_cons_succ, Bool.and_eq_true] at h
      cases p with
      | zero =>
        cases adjs with
        | nil => simpa using h.1
        | cons l ls => simpa using h.1
      | succ p =>
        have := ih (i + 1) adjs.tail n h.2 p (by omega) (by simpa using hp)
        rw [show i + (p + 1) + 1 = i + 1 + p + 1 by omega]
        cases adjs with
        | nil => simpa using this
        | cons l ls => simpa using this

/-- Edges described by the adjacency lists, starting at row `i`. -/
noncomputable def flat (ls : List (List ℕ)) : ℕ → List (ℕ × ℕ) :=
  List.rec (motive := fun _ => ℕ → List (ℕ × ℕ)) (fun _ => [])
    (fun l _ ih i => l.map (fun j => (i, j)) ++ ih (i + 1)) ls

theorem flat_cons (l : List ℕ) (ls : List (List ℕ)) (i : ℕ) :
    flat (l :: ls) i = l.map (fun j => (i, j)) ++ flat ls (i + 1) := rfl

theorem flat_mem : ∀ (ls : List (List ℕ)) (i p j : ℕ), j ∈ ls.getD p [] → (i + p, j) ∈ flat ls i := by
  intro ls
  induction ls with
  | nil => intro i p j h; simp at h
  | cons l ls ih =>
    intro i p j h
    rw [flat_cons, List.mem_append]
    cases p with
    | zero => left; simpa using h
    | succ p =>
      right
      rw [show i + (p + 1) = i + 1 + p by omega]
      exact ih (i + 1) p j (by simpa using h)

end G509.EX
