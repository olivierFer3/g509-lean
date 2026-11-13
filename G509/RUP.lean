/-
Copyright (c) 2026 olivierFer3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.LRAT

/-!
# A kernel-reducible RUP checker with static tables

Written for this formalization (no code taken from elsewhere; reuses `LR.litT`, `LR.neg`, `LR.clauseT`,
`LR.SatF`, `LR.litT_neg` from `G509/LRAT.lean`).

Differences with `G509/LRAT.lean` (dynamic clause database, insertions):
* a proof chunk is given by a *static table* `t : Tb` (a literal binary tree,
  already in constructor form): entries `0 … m-1` = base clauses (selected clauses of `F` and
  imported clauses), entries `m …` = derived clauses, in order;
* step `i` may only use indices `< i` (checked), and its clause `get t i` must be
  RUP with respect to the hinted clauses;
* partial assignment: a natural number `A` whose bit `l` means "literal `l` is false";
* all functions are written directly with the recursors (`Tb.rec`, `List.rec`,
  `Bool.rec`) and the `Nat` operations that the kernel accelerates with GMP (`Nat.land`, `Nat.lor`,
  `Nat.shiftRight`, `Nat.pow`, `Nat.beq`, `Nat.blt`).

Soundness: `chunk_sound`.
-/

namespace RV

open LR (litT neg clauseT SatF litT_neg)

inductive Tb where
  | lf : List Nat → Tb
  | nd : Tb → Tb → Tb

/-- Entry `k` of the table (bits of `k`, least significant first). -/
noncomputable def get (t : Tb) : Nat → List Nat :=
  Tb.rec (motive := fun _ => Nat → List Nat) (fun c _ => c)
    (fun _ _ ia ib k => Bool.rec (motive := fun _ => List Nat) (ib (Nat.shiftRight k 1))
      (ia (Nat.shiftRight k 1)) (Nat.beq (Nat.land k 1) 0)) t

/-- Bit `x` of `A`. -/
def bt (A x : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight A x) 1) 1

theorem bt_eq (A x : Nat) : bt A x = A.testBit x := by
  unfold bt
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h1 : Nat.land (Nat.shiftRight A x) 1 = A / 2 ^ x % 2 := by
    show (A >>> x) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [h1]
  rcases Nat.mod_two_eq_zero_or_one (A / 2 ^ x) with h | h <;> rw [h] <;> rfl

theorem bt_lor (a b l : Nat) : bt (Nat.lor a b) l = (bt a l || bt b l) := by
  rw [bt_eq, bt_eq, bt_eq]; exact Nat.testBit_or a b l

theorem bt_pow (x l : Nat) : bt (Nat.pow 2 x) l = decide (x = l) := by
  rw [bt_eq]; exact Nat.testBit_two_pow

theorem bt_zero (l : Nat) : bt 0 l = false := by
  rw [bt_eq]; exact Nat.zero_testBit l

/-- `A` is compatible with `τ`: the marked literals are false. -/
def Agree (τ : Nat → Bool) (A : Nat) : Prop := ∀ l, bt A l = true → litT τ l = false

theorem agree_lor (τ : Nat → Bool) (A u : Nat) (hA : Agree τ A) (hu : litT τ u = false) :
    Agree τ (Nat.lor A (Nat.pow 2 u)) := by
  intro l h
  rw [bt_lor, bt_pow, Bool.or_eq_true] at h
  rcases h with h | h
  · exact hA l h
  · have : u = l := of_decide_eq_true h
    subst this; exact hu

/-! ## Propagation -/

/-- `0`: all literals of `D` are false; `1`: at least two are not false;
`x + 2`: `x` is the only literal that is not false. -/
noncomputable def nf (A : Nat) (D : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun x _ ih => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) 1 (x + 2) (Nat.beq ih 0)) ih (bt A x)) D

theorem nf_cons (A x : Nat) (D : List Nat) : nf A (x :: D) =
    Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) 1 (x + 2) (Nat.beq (nf A D) 0)) (nf A D) (bt A x) := rfl

theorem nf_zero (A : Nat) : ∀ D, nf A D = 0 → ∀ x ∈ D, bt A x = true := by
  intro D
  induction D with
  | nil => intro _ x hx; simp at hx
  | cons y D ih =>
    intro h x hx
    rw [nf_cons] at h
    cases hb : bt A y
    · rw [hb] at h
      cases hc : Nat.beq (nf A D) 0
      · rw [hc] at h; exact absurd h (Nat.succ_ne_zero _)
      · rw [hc] at h; exact absurd h (Nat.succ_ne_zero _)
    · rw [hb] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hb
      · exact ih h x hx

theorem nf_unit (A : Nat) : ∀ D y, nf A D = y + 2 → ∀ x ∈ D, bt A x = false → x = y := by
  intro D
  induction D with
  | nil => intro y _ x hx; simp at hx
  | cons z D ih =>
    intro y h x hx hbx
    rw [nf_cons] at h
    cases hb : bt A z
    · rw [hb] at h
      cases hc : Nat.beq (nf A D) 0
      · rw [hc] at h; have h2 : 1 = y + 2 := h; omega
      · rw [hc] at h
        have hzy : z = y := by have h2 : z + 2 = y + 2 := h; omega
        have h0 : nf A D = 0 := Nat.eq_of_beq_eq_true hc
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hzy
        · have := nf_zero A D h0 x hx; rw [hbx] at this; exact Bool.noConfusion this
    · rw [hb] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hb] at hbx; exact Bool.noConfusion hbx
      · exact ih y h x hx hbx

/-- Elementary step: `s = nf A D`. -/
noncomputable def pstep (s : Nat) (k : Nat → Bool) (A : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (k (Nat.lor A (Nat.pow 2 (neg (s - 2))))) false (Nat.beq s 1))
    true (Nat.beq s 0)

/-- Unit propagation along the hints `H` (all `< i`). -/
noncomputable def prop (t : Tb) (i : Nat) (H : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun h _ ih A => Bool.rec (motive := fun _ => Bool) false (pstep (nf A (get t h)) ih A)
      (Nat.blt h i)) H

theorem prop_cons (t : Tb) (i h : Nat) (H : List Nat) (A : Nat) : prop t i (h :: H) A =
    Bool.rec (motive := fun _ => Bool) false (pstep (nf A (get t h)) (prop t i H) A)
      (Nat.blt h i) := rfl

/-- The entries `< i` of the table are true under `τ`. -/
def Good (τ : Nat → Bool) (t : Tb) (i : Nat) : Prop := ∀ j, j < i → clauseT τ (get t j) = true

theorem prop_sound (τ : Nat → Bool) (t : Tb) (i : Nat) (hg : Good τ t i) :
    ∀ (H : List Nat) (A : Nat), Agree τ A → prop t i H A = true → False := by
  intro H
  induction H with
  | nil => intro A _ h; exact Bool.noConfusion h
  | cons h H ih =>
    intro A hA hp
    rw [prop_cons] at hp
    cases hlt : Nat.blt h i
    · rw [hlt] at hp; exact Bool.noConfusion hp
    · rw [hlt] at hp
      have hhi : h < i := by simpa [Nat.blt_eq] using hlt
      have hD := hg h hhi
      unfold clauseT at hD
      obtain ⟨x, hx, hxt⟩ := List.any_eq_true.mp hD
      have hbx : bt A x = false := by
        cases hb : bt A x
        · rfl
        · have := hA x hb; rw [hxt] at this; exact Bool.noConfusion this
      unfold pstep at hp
      generalize hs : nf A (get t h) = s at hp
      cases h0 : Nat.beq s 0
      · rw [h0] at hp
        cases h1 : Nat.beq s 1
        · rw [h1] at hp
          have s0 : s ≠ 0 := Nat.ne_of_beq_eq_false h0
          have s1 : s ≠ 1 := Nat.ne_of_beq_eq_false h1
          have hy : nf A (get t h) = (s - 2) + 2 := by omega
          have hxy := nf_unit A _ _ hy x hx hbx
          subst hxy
          refine ih _ (agree_lor τ A _ hA ?_) hp
          rw [litT_neg, hxt]; rfl
        · rw [h1] at hp; exact Bool.noConfusion hp
      · have s0 : s = 0 := Nat.eq_of_beq_eq_true h0
        subst s0
        have := nf_zero A _ hs x hx
        rw [hbx] at this; exact Bool.noConfusion this

/-- Mask of the clause: all its literals false. -/
noncomputable def msk (C : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.lor ih (Nat.pow 2 x)) C

theorem agree_msk (τ : Nat → Bool) : ∀ C : List Nat, (∀ x ∈ C, litT τ x = false) →
    Agree τ (msk C) := by
  intro C
  induction C with
  | nil => intro _ l h; rw [show msk [] = 0 from rfl, bt_zero] at h; exact Bool.noConfusion h
  | cons x C ih =>
    intro hC
    show Agree τ (Nat.lor (msk C) (Nat.pow 2 x))
    exact agree_lor τ _ x (ih fun y hy => hC y (by simp [hy])) (hC x (by simp))

theorem rup_sound (τ : Nat → Bool) (t : Tb) (i : Nat) (hg : Good τ t i) (C H : List Nat)
    (h : prop t i H (msk C) = true) : clauseT τ C = true := by
  cases hc : clauseT τ C
  · exfalso
    have hall : ∀ x ∈ C, litT τ x = false := by
      intro x hx
      cases hl : litT τ x
      · rfl
      · have : clauseT τ C = true := by
          unfold clauseT; rw [List.any_eq_true]; exact ⟨x, hx, hl⟩
        rw [hc] at this; exact Bool.noConfusion this
    exact prop_sound τ t i hg H _ (agree_msk τ C hall) h
  · rfl

/-! ## Steps, base, exports -/

/-- Steps: the list `hs` gives the hints of each derived clause `i, i+1, …`. -/
noncomputable def chk (t : Tb) (hs : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun H _ ih i => Bool.rec (motive := fun _ => Bool) false (ih (i + 1))
      (prop t i H (msk (get t i)))) hs

noncomputable def len (l : List α) : Nat := List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => ih + 1) l

theorem chk_sound (τ : Nat → Bool) (t : Tb) : ∀ (hs : List (List Nat)) (i : Nat),
    Good τ t i → chk t hs i = true → Good τ t (i + len hs) := by
  intro hs
  induction hs with
  | nil => intro i h _; exact h
  | cons H hs ih =>
    intro i hg hc
    have e : chk t (H :: hs) i = Bool.rec (motive := fun _ => Bool) false (chk t hs (i + 1))
      (prop t i H (msk (get t i))) := rfl
    rw [e] at hc
    cases hp : prop t i H (msk (get t i))
    · rw [hp] at hc; exact Bool.noConfusion hc
    · rw [hp] at hc
      have hci := rup_sound τ t i hg _ _ hp
      have hg' : Good τ t (i + 1) := by
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact hg j hj
        · exact hci
      have := ih (i + 1) hg' hc
      have e2 : len (H :: hs) = len hs + 1 := rfl
      rw [e2, show i + (len hs + 1) = i + 1 + len hs by omega]; exact this

/-- Equality of lists of naturals. -/
noncomputable def eqL (a : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => Bool.rec (motive := fun _ => Bool) false (ih ys) (Nat.beq x y)) b) a

theorem eqL_sound : ∀ a b : List Nat, eqL a b = true → a = b := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons y ys => exact Bool.noConfusion h
  | cons x xs ih =>
    intro b h
    cases b with
    | nil => exact Bool.noConfusion h
    | cons y ys =>
      have e : eqL (x :: xs) (y :: ys) =
        Bool.rec (motive := fun _ => Bool) false (eqL xs ys) (Nat.beq x y) := rfl
      rw [e] at h
      cases hb : Nat.beq x y
      · rw [hb] at h; exact Bool.noConfusion h
      · rw [hb] at h
        rw [Nat.eq_of_beq_eq_true hb, ih ys h]

/-- The table starts with the clauses `bs` (from index `i` on). -/
noncomputable def baseOK (t : Tb) (bs : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ ih i => Bool.rec (motive := fun _ => Bool) false (ih (i + 1)) (eqL (get t i) c)) bs

theorem baseOK_sound (τ : Nat → Bool) (t : Tb) : ∀ (bs : List (List Nat)) (i : Nat),
    Good τ t i → (∀ c ∈ bs, clauseT τ c = true) → baseOK t bs i = true → Good τ t (i + len bs) := by
  intro bs
  induction bs with
  | nil => intro i h _ _; exact h
  | cons c bs ih =>
    intro i hg hbs hb
    have e : baseOK t (c :: bs) i = Bool.rec (motive := fun _ => Bool) false (baseOK t bs (i + 1))
      (eqL (get t i) c) := rfl
    rw [e] at hb
    cases he : eqL (get t i) c
    · rw [he] at hb; exact Bool.noConfusion hb
    · rw [he] at hb
      have hci : clauseT τ (get t i) = true := by
        rw [eqL_sound _ _ he]; exact hbs c (by simp)
      have hg' : Good τ t (i + 1) := by
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact hg j hj
        · exact hci
      have := ih (i + 1) hg' (fun d hd => hbs d (by simp [hd])) hb
      have e2 : len (c :: bs) = len bs + 1 := rfl
      rw [e2, show i + (len bs + 1) = i + 1 + len bs by omega]; exact this

/-- Exports: `(j, c)` with `j < n` and `get t j = c`. -/
noncomputable def expOK (t : Tb) (n : Nat) (es : List (Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false ih (eqL (get t p.1) p.2)) (Nat.blt p.1 n)) es

theorem expOK_sound (τ : Nat → Bool) (t : Tb) (n : Nat) (hg : Good τ t n) :
    ∀ es : List (Nat × List Nat), expOK t n es = true → ∀ p ∈ es, clauseT τ p.2 = true := by
  intro es
  induction es with
  | nil => intro _ p hp; simp at hp
  | cons q es ih =>
    intro h p hp
    have e : expOK t n (q :: es) = Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (expOK t n es) (eqL (get t q.1) q.2))
      (Nat.blt q.1 n) := rfl
    rw [e] at h
    cases hl : Nat.blt q.1 n
    · rw [hl] at h; exact Bool.noConfusion h
    · rw [hl] at h
      cases he : eqL (get t q.1) q.2
      · rw [he] at h; exact Bool.noConfusion h
      · rw [he] at h
        rcases List.mem_cons.mp hp with rfl | hp
        · rw [← eqL_sound _ _ he]
          exact hg _ (by simpa [Nat.blt_eq] using hl)
        · exact ih h p hp

/-! ## Complete chunk -/

noncomputable def app (a b : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) b (fun x _ ih => x :: ih) a

theorem mem_app : ∀ (a b : List (List Nat)) c, c ∈ app a b → c ∈ a ∨ c ∈ b := by
  intro a
  induction a with
  | nil => intro b c h; exact Or.inr h
  | cons x a ih =>
    intro b c h
    have e : app (x :: a) b = x :: app a b := rfl
    rw [e] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl (by simp)
    · rcases ih b c h with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr h

/-- Selected clauses of `FT`, with the check `j < NF`. -/
noncomputable def sel (FT : Tb) (NF : Nat) (fs : List Nat) : Option (List (List Nat)) :=
  List.rec (motive := fun _ => Option (List (List Nat))) (some [])
    (fun j _ ih => Bool.rec (motive := fun _ => Option (List (List Nat))) none
      (Option.rec (motive := fun _ => Option (List (List Nat))) none (fun l => some (get FT j :: l)) ih)
      (Nat.blt j NF)) fs

theorem sel_sound (τ : Nat → Bool) (FT : Tb) (NF : Nat) (hF : Good τ FT NF) :
    ∀ (fs : List Nat) (l : List (List Nat)), sel FT NF fs = some l → ∀ c ∈ l, clauseT τ c = true := by
  intro fs
  induction fs with
  | nil => intro l h c hc; cases h; simp at hc
  | cons j fs ih =>
    intro l h c hc
    have e : sel FT NF (j :: fs) = Bool.rec (motive := fun _ => Option (List (List Nat))) none
      (Option.rec (motive := fun _ => Option (List (List Nat))) none (fun l => some (get FT j :: l))
        (sel FT NF fs)) (Nat.blt j NF) := rfl
    rw [e] at h
    cases hl : Nat.blt j NF
    · rw [hl] at h; exact absurd h (by simp)
    · rw [hl] at h
      cases hs : sel FT NF fs with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some l' =>
        rw [hs] at h
        cases h
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hF j (by simpa [Nat.blt_eq] using hl)
        · exact ih l' hs c hc

noncomputable def check2 (t : Tb) (bs : List (List Nat)) (hs : List (List Nat))
    (es : List (Nat × List Nat)) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false (expOK t (Nat.add (len bs) (len hs)) es)
      (chk t hs (len bs)))
    (baseOK t bs 0)

/-- Checking a chunk. -/
noncomputable def chunkCheck (FT : Tb) (NF : Nat) (t : Tb) (fs : List Nat) (imp : List (List Nat))
    (hs : List (List Nat)) (es : List (Nat × List Nat)) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun l => check2 t (app l imp) hs es) (sel FT NF fs)

theorem chunk_sound (FT : Tb) (NF : Nat) (t : Tb) (fs : List Nat) (imp : List (List Nat))
    (hs : List (List Nat)) (es : List (Nat × List Nat))
    (h : chunkCheck FT NF t fs imp hs es = true) (τ : Nat → Bool) (hF : Good τ FT NF)
    (hi : ∀ c ∈ imp, clauseT τ c = true) : ∀ p ∈ es, clauseT τ p.2 = true := by
  unfold chunkCheck at h
  cases hs' : sel FT NF fs with
  | none => rw [hs'] at h; exact Bool.noConfusion h
  | some l =>
    rw [hs'] at h
    have h' : check2 t (app l imp) hs es = true := h
    unfold check2 at h'
    have hl := sel_sound τ FT NF hF fs l hs'
    have hbs : ∀ c ∈ app l imp, clauseT τ c = true := by
      intro c hc
      rcases mem_app l imp c hc with hc | hc
      · exact hl c hc
      · exact hi c hc
    cases hb : baseOK t (app l imp) 0
    · rw [hb] at h'; exact Bool.noConfusion h'
    · rw [hb] at h'
      have g0 : Good τ t 0 := fun j hj => absurd hj (Nat.not_lt_zero j)
      have g1 := baseOK_sound τ t _ 0 g0 hbs hb
      rw [Nat.zero_add] at g1
      cases hc : chk t hs (len (app l imp))
      · rw [hc] at h'; exact Bool.noConfusion h'
      · rw [hc] at h'
        have g2 := chk_sound τ t hs _ g1 hc
        exact expOK_sound τ t _ g2 es h'

/-- Table of `F`: if `baseOK FT F 0`, all entries `< len F` are true. -/
theorem ft_good (FT : Tb) (F : List (List Nat)) (h : baseOK FT F 0 = true) (τ : Nat → Bool)
    (hτ : SatF τ F) : Good τ FT (len F) := by
  have := baseOK_sound τ FT F 0 (fun j hj => absurd hj (Nat.not_lt_zero j)) hτ h
  rwa [Nat.zero_add] at this

end RV

namespace RV

open LR (litT neg clauseT SatF litT_neg)

noncomputable def snds (es : List (Nat × List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) [] (fun p _ ih => p.2 :: ih) es

theorem mem_snds : ∀ (es : List (Nat × List Nat)) c, c ∈ snds es → ∃ p ∈ es, p.2 = c := by
  intro es
  induction es with
  | nil => intro c h; simp [snds] at h
  | cons p es ih =>
    intro c h
    have e : snds (p :: es) = p.2 :: snds es := rfl
    rw [e] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨p, by simp, rfl⟩
    · obtain ⟨q, hq, rfl⟩ := ih c h; exact ⟨q, by simp [hq], rfl⟩

/-- Chaining: if the exports of the previous chunk are consequences of `F`, so are those
of the current chunk. -/
theorem chunk_step (FT : Tb) (NF : Nat) (t : Tb) (fs : List Nat) (prev : List (Nat × List Nat))
    (hs : List (List Nat)) (es : List (Nat × List Nat))
    (h : chunkCheck FT NF t fs (snds prev) hs es = true) (τ : Nat → Bool) (hF : Good τ FT NF)
    (hp : ∀ p ∈ prev, clauseT τ p.2 = true) : ∀ p ∈ es, clauseT τ p.2 = true := by
  refine chunk_sound FT NF t fs (snds prev) hs es h τ hF ?_
  intro c hc
  obtain ⟨q, hq, rfl⟩ := mem_snds prev c hc
  exact hp q hq

theorem not_empty (τ : Nat → Bool) (es : List (Nat × List Nat)) (j : Nat) (hj : (j, []) ∈ es)
    (h : ∀ p ∈ es, clauseT τ p.2 = true) : False := by
  have := h _ hj
  simp [LR.clauseT] at this

end RV

/-! ## Decoding of compact data (to speed up elaboration; no effect on
soundness: the theorems hold for whatever lists are given) -/

namespace RV

/-- 20-bit tokens, nonzero, at most `f`. -/
noncomputable def U (f : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih n => Bool.rec (motive := fun _ => List Nat)
      (Nat.mod n 1048576 :: ih (Nat.shiftRight n 20)) [] (Nat.beq n 0)) f

/-- Like `U`, with tokens decreased by 1 (indices). -/
noncomputable def UH (f : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih n => Bool.rec (motive := fun _ => List Nat)
      (Nat.sub (Nat.mod n 1048576) 1 :: ih (Nat.shiftRight n 20)) [] (Nat.beq n 0)) f

end RV

/-! ## Construction of the table by the kernel, from a flat list (elaborating a
nested literal tree is too slow). No property of `build` is needed for
soundness: `chunk_sound` holds for every table. -/

namespace RV

/-- `(evens, odds)`: elements of even / odd index. -/
noncomputable def spl (l : List (List Nat)) : List (List Nat) × List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat) × List (List Nat)) ([], [])
    (fun x _ ih => (x :: ih.2, ih.1)) l

noncomputable def build (d : Nat) : List (List Nat) → Tb :=
  Nat.rec (motive := fun _ => List (List Nat) → Tb)
    (fun l => Tb.lf (List.rec (motive := fun _ => List Nat) [] (fun x _ _ => x) l))
    (fun _ ih l => Tb.nd (ih (spl l).1) (ih (spl l).2)) d

end RV

/-! ## Direct imports from several earlier chunks (no transit) -/

namespace RV

open LR (clauseT)

noncomputable def appE (a b : List (Nat × List Nat)) : List (Nat × List Nat) :=
  List.rec (motive := fun _ => List (Nat × List Nat)) b (fun x _ ih => x :: ih) a

theorem appE_l (b : List (Nat × List Nat)) (p : Nat × List Nat) :
    ∀ a, p ∈ a → p ∈ appE a b := by
  intro a
  induction a with
  | nil => intro h; simp at h
  | cons x a ih =>
    intro h
    show p ∈ x :: appE a b
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (ih h)

theorem appE_r (b : List (Nat × List Nat)) (p : Nat × List Nat) (hb : p ∈ b) :
    ∀ a, p ∈ appE a b := by
  intro a
  induction a with
  | nil => exact hb
  | cons x a ih => show p ∈ x :: appE a b; exact List.mem_cons_of_mem _ ih

theorem all_app (τ : Nat → Bool) (a b : List (List Nat)) (ha : ∀ c ∈ a, clauseT τ c = true)
    (hb : ∀ c ∈ b, clauseT τ c = true) : ∀ c ∈ app a b, clauseT τ c = true := by
  intro c hc
  rcases mem_app a b c hc with h | h
  · exact ha c h
  · exact hb c h

theorem all_snds (τ : Nat → Bool) (es : List (Nat × List Nat))
    (h : ∀ p ∈ es, clauseT τ p.2 = true) : ∀ c ∈ snds es, clauseT τ c = true := by
  intro c hc
  obtain ⟨q, hq, rfl⟩ := mem_snds es c hc
  exact h q hq

theorem all_nil (τ : Nat → Bool) : ∀ c ∈ ([] : List (List Nat)), clauseT τ c = true := by
  intro c h; simp at h

end RV
