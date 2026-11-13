/-
Copyright (c) 2026 olivierFer3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
/-!
# A kernel-reducible LRAT (RUP) checker

Written for this formalization (no code taken from elsewhere). All functions are defined by structural
recursion (on lists or on a fixed depth `ℕ`), without well-founded recursion, so that
`decide +kernel` can evaluate them. The checker from Lean core
(`Std.Tactic.BVDecide.LRAT.check`) cannot be used this way: its loop `check.go` is defined
by well-founded recursion and kernel reduction gets stuck on it.

* Literals: `2v` (variable `v` true) and `2v+1` (variable `v` false), `v ≥ 1` (DIMACS).
* Partial assignment: a natural number `A` whose bit `l` means "literal `l` is true"
  (operations `|||`, `2^·`, `testBit`, GMP-accelerated in the kernel).
* Clause database: binary tree indexed by the bits of the clause id (depth `depth`).
* A step = `(id, clause, hints)`; the clause is checked by RUP unit propagation on the
  hinted clauses. Deletions are ignored (this does not affect soundness).
* Soundness: `Entails F C := ∀ τ, τ ⊨ F → τ ⊨ C`. `chunk_sound`: if `checkChunk` returns
  `true`, all exported clauses are consequences of `F`, provided the imported clauses
  are. `unsat_of_check`: if the empty clause is derived, `F` is unsatisfiable.
-/

namespace LR

/-- Value of a literal under a total assignment. -/
def litT (τ : Nat → Bool) (l : Nat) : Bool := if l % 2 = 0 then τ (l / 2) else !τ (l / 2)

def clauseT (τ : Nat → Bool) (c : List Nat) : Bool := c.any (litT τ)

def neg (l : Nat) : Nat := if l % 2 = 0 then l + 1 else l - 1

theorem litT_neg (τ : Nat → Bool) (l : Nat) : litT τ (neg l) = !litT τ l := by
  unfold litT neg
  by_cases h : l % 2 = 0
  · have h1 : (l + 1) % 2 = 1 := by omega
    have h2 : (l + 1) / 2 = l / 2 := by omega
    simp [h, h1, h2]
  · have h1 : (l - 1) % 2 = 0 := by omega
    have h2 : (l - 1) / 2 = l / 2 := by omega
    simp [h, h1, h2]

/-- The partial assignment `A` is compatible with `τ`. -/
def Agree (τ : Nat → Bool) (A : Nat) : Prop := ∀ l, A.testBit l = true → litT τ l = true

theorem agree_zero (τ : Nat → Bool) : Agree τ 0 := by
  intro l h; simp at h

theorem agree_or (τ : Nat → Bool) (A u : Nat) (hA : Agree τ A) (hu : litT τ u = true) :
    Agree τ (A ||| 2 ^ u) := by
  intro l h
  rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at h
  rcases h with h | h
  · exact hA l h
  · have : u = l := of_decide_eq_true h
    subst this; exact hu

/-! ## Clause database -/

inductive Trie where
  | leaf : Trie
  | node : Option (List Nat) → Trie → Trie → Trie

namespace Trie

def v : Trie → Option (List Nat)
  | leaf => none
  | node x _ _ => x
def l : Trie → Trie
  | leaf => leaf
  | node _ a _ => a
def r : Trie → Trie
  | leaf => leaf
  | node _ _ b => b

def find : Nat → Trie → Nat → Option (List Nat)
  | 0, t, _ => t.v
  | d + 1, t, k => if k % 2 = 0 then find d t.l (k / 2) else find d t.r (k / 2)

def insert : Nat → Trie → Nat → List Nat → Trie
  | 0, t, _, c => node (some c) t.l t.r
  | d + 1, t, k, c =>
    if k % 2 = 0 then node t.v (insert d t.l (k / 2) c) t.r
    else node t.v t.l (insert d t.r (k / 2) c)

theorem find_insert (d : Nat) (t : Trie) (k k' : Nat) (c D : List Nat)
    (h : find d (insert d t k c) k' = some D) : D = c ∨ find d t k' = some D := by
  induction d generalizing t k k' with
  | zero =>
    left; simp [find, insert, v] at h; exact h.symm
  | succ d ih =>
    unfold insert at h
    unfold find at h ⊢
    by_cases hk : k % 2 = 0 <;> by_cases hk' : k' % 2 = 0 <;> simp [hk, hk', l, r] at h ⊢
    · exact ih _ _ _ h
    · exact Or.inr h
    · exact Or.inr h
    · exact ih _ _ _ h

theorem find_leaf : ∀ (d k : Nat), find d leaf k = none := by
  intro d
  induction d with
  | zero => intro k; rfl
  | succ d ih => intro k; unfold find; split <;> exact ih _

end Trie

/-- Depth of the tree (ids < 2^22 do not collide; collisions would not affect
soundness). -/
def depth : Nat := 22

/-- All clauses of the database are true under `τ`. -/
def Good (τ : Nat → Bool) (db : Trie) : Prop :=
  ∀ k D, Trie.find depth db k = some D → clauseT τ D = true

theorem good_leaf (τ : Nat → Bool) : Good τ Trie.leaf := by
  intro k D h; rw [Trie.find_leaf] at h; exact absurd h (by simp)

theorem good_insert (τ : Nat → Bool) (db : Trie) (k : Nat) (c : List Nat)
    (h : Good τ db) (hc : clauseT τ c = true) : Good τ (Trie.insert depth db k c) := by
  intro k' D hD
  rcases Trie.find_insert depth db k k' c D hD with rfl | h'
  · exact hc
  · exact h k' D h'

/-! ## Unit propagation -/

/-- Literals of `D` that are not false under `A`. -/
def nonFalse (A : Nat) (D : List Nat) : List Nat := D.filter (fun x => !A.testBit (neg x))

def propagate (db : Trie) : Nat → List Nat → Bool
  | _, [] => false
  | A, h :: hs =>
    match Trie.find depth db h with
    | none => false
    | some D =>
      match nonFalse A D with
      | [] => true
      | [u] => propagate db (A ||| 2 ^ u) hs
      | _ :: _ :: _ => false

theorem true_mem_nonFalse (τ : Nat → Bool) (A : Nat) (hA : Agree τ A) (D : List Nat) (x : Nat)
    (hx : x ∈ D) (hxt : litT τ x = true) : x ∈ nonFalse A D := by
  unfold nonFalse
  rw [List.mem_filter]
  refine ⟨hx, ?_⟩
  cases hb : A.testBit (neg x)
  · rfl
  · have := hA _ hb
    rw [litT_neg, hxt] at this
    exact absurd this (by decide)

theorem propagate_sound (τ : Nat → Bool) (db : Trie) (hdb : Good τ db) :
    ∀ (hs : List Nat) (A : Nat), Agree τ A → propagate db A hs = true → False := by
  intro hs
  induction hs with
  | nil => intro A _ h; simp [propagate] at h
  | cons h hs ih =>
    intro A hA hp
    unfold propagate at hp
    split at hp
    · exact absurd hp (by decide)
    · rename_i D hD
      have hDt := hdb h D hD
      unfold clauseT at hDt
      rw [List.any_eq_true] at hDt
      obtain ⟨x, hx, hxt⟩ := hDt
      have hxm := true_mem_nonFalse τ A hA D x hx hxt
      split at hp
      · rename_i he; rw [he] at hxm; simp at hxm
      · rename_i u he
        rw [he] at hxm
        have hxu : x = u := by simpa using hxm
        subst hxu
        exact ih _ (agree_or τ A x hA hxt) hp
      · exact absurd hp (by decide)

/-- Initial assignment: negation of the candidate clause. -/
def initA (A : Nat) : List Nat → Nat
  | [] => A
  | x :: xs => initA (A ||| 2 ^ neg x) xs

theorem agree_initA (τ : Nat → Bool) :
    ∀ (C : List Nat) (A : Nat), Agree τ A → (∀ x ∈ C, litT τ x = false) → Agree τ (initA A C) := by
  intro C
  induction C with
  | nil => intro A hA _; exact hA
  | cons x xs ih =>
    intro A hA hC
    apply ih
    · apply agree_or τ A _ hA
      rw [litT_neg, hC x (by simp)]; rfl
    · intro y hy; exact hC y (by simp [hy])

def rup (db : Trie) (C H : List Nat) : Bool := propagate db (initA 0 C) H

theorem rup_sound (τ : Nat → Bool) (db : Trie) (hdb : Good τ db) (C H : List Nat)
    (h : rup db C H = true) : clauseT τ C = true := by
  cases hc : clauseT τ C
  · exfalso
    have hall : ∀ x ∈ C, litT τ x = false := by
      intro x hx
      cases hl : litT τ x
      · rfl
      · have : clauseT τ C = true := by
          unfold clauseT; rw [List.any_eq_true]; exact ⟨x, hx, hl⟩
        rw [hc] at this; exact absurd this (by decide)
    exact propagate_sound τ db hdb H _ (agree_initA τ C 0 (agree_zero τ) hall) h
  · rfl

/-! ## Decoding of steps (compact integers, 20-bit tokens, all ≥ 1) -/

def tokens : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else (n % 1048576) :: tokens f (n / 1048576)

/-- An encoded step: tokens `id, k+1, l₁ … l_k, h₁ … h_m`. -/
def decodeStep (s : Nat) : Nat × List Nat × List Nat :=
  match tokens 100000 s with
  | i :: k :: rest => (i, rest.take (k - 1), rest.drop (k - 1))
  | _ => (0, [], [])

/-- Runs the steps; `none` as soon as a step fails. -/
def derive (db : Trie) : List Nat → Option Trie
  | [] => some db
  | s :: ss =>
    match decodeStep s with
    | (i, C, H) => if rup db C H then derive (Trie.insert depth db i C) ss else none

theorem derive_sound (τ : Nat → Bool) :
    ∀ (ss : List Nat) (db db' : Trie), Good τ db → derive db ss = some db' → Good τ db' := by
  intro ss
  induction ss with
  | nil => intro db db' h e; simp [derive] at e; subst e; exact h
  | cons s ss ih =>
    intro db db' h e
    unfold derive at e
    split at e
    rename_i i C H _
    split at e
    · rename_i hr
      exact ih _ _ (good_insert τ db i C h (rup_sound τ db h C H hr)) e
    · exact absurd e (by simp)

/-- Inserts a list of clauses `(id, clause)`. -/
def insertAll (db : Trie) : List (Nat × List Nat) → Trie
  | [] => db
  | p :: ps => insertAll (Trie.insert depth db p.1 p.2) ps

theorem good_insertAll (τ : Nat → Bool) :
    ∀ (ps : List (Nat × List Nat)) (db : Trie), Good τ db → (∀ p ∈ ps, clauseT τ p.2 = true) →
      Good τ (insertAll db ps) := by
  intro ps
  induction ps with
  | nil => intro db h _; exact h
  | cons p ps ih =>
    intro db h hp
    exact ih _ (good_insert τ db p.1 p.2 h (hp p (by simp))) (fun q hq => hp q (by simp [hq]))

/-- DIMACS numbering of the clauses of `F`: `1, 2, …`. -/
def number : Nat → List (List Nat) → List (Nat × List Nat)
  | _, [] => []
  | i, c :: cs => (i, c) :: number (i + 1) cs

theorem mem_number : ∀ (F : List (List Nat)) (i : Nat) (p : Nat × List Nat),
    p ∈ number i F → p.2 ∈ F := by
  intro F
  induction F with
  | nil => intro i p h; simp [number] at h
  | cons c cs ih =>
    intro i p h
    simp only [number, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (ih _ _ h)

def SatF (τ : Nat → Bool) (F : List (List Nat)) : Prop := ∀ c ∈ F, clauseT τ c = true

def Entails (F : List (List Nat)) (C : List Nat) : Prop := ∀ τ, SatF τ F → clauseT τ C = true

/-- A chunk: database = numbered `F` + imported clauses; then the steps; then a check that
each exported clause is in the final database under its id. -/
def checkChunk (F : List (List Nat)) (imports : List (Nat × List Nat)) (steps : List Nat)
    (exports : List (Nat × List Nat)) : Bool :=
  match derive (insertAll (insertAll Trie.leaf (number 1 F)) imports) steps with
  | none => false
  | some db => exports.all (fun p => Trie.find depth db p.1 == some p.2)

theorem chunk_sound (F : List (List Nat)) (imports : List (Nat × List Nat)) (steps : List Nat)
    (exports : List (Nat × List Nat)) (h : checkChunk F imports steps exports = true)
    (himp : ∀ p ∈ imports, Entails F p.2) : ∀ p ∈ exports, Entails F p.2 := by
  intro p hp τ hτ
  unfold checkChunk at h
  split at h
  · exact absurd h (by decide)
  · rename_i db hdb
    have g0 : Good τ (insertAll Trie.leaf (number 1 F)) :=
      good_insertAll τ _ _ (good_leaf τ) (fun q hq => hτ _ (mem_number F 1 q hq))
    have g1 := good_insertAll τ imports _ g0 (fun q hq => himp q hq τ hτ)
    have g2 := derive_sound τ steps _ db g1 hdb
    have he := List.all_eq_true.mp h p hp
    have hf : Trie.find depth db p.1 = some p.2 := by simpa using he
    exact g2 _ _ hf

theorem unsat_of_entails_empty (F : List (List Nat)) (h : Entails F []) :
    ∀ τ, ¬ SatF τ F := by
  intro τ hτ
  have := h τ hτ
  simp [clauseT] at this


/-! ## "Fast" versions written directly with the recursors (`Nat.rec`, `List.rec`)

Structural compilation via `brecOn` is memory-hungry for the kernel. The functions
below compute the same thing with the raw recursors; we prove that they are equal
to the previous versions, and the kernel then evaluates the fast versions. -/

noncomputable def findF (d : Nat) : Trie → Nat → Option (List Nat) :=
  Nat.rec (motive := fun _ => Trie → Nat → Option (List Nat)) (fun t _ => t.v)
    (fun _ ih t k => if k % 2 = 0 then ih t.l (k / 2) else ih t.r (k / 2)) d

theorem findF_eq : ∀ d t k, findF d t k = Trie.find d t k := by
  intro d
  induction d with
  | zero => intro t k; rfl
  | succ d ih =>
    intro t k
    show (if k % 2 = 0 then findF d t.l (k / 2) else findF d t.r (k / 2)) = _
    simp only [ih, Trie.find]

noncomputable def insertF (d : Nat) : Trie → Nat → List Nat → Trie :=
  Nat.rec (motive := fun _ => Trie → Nat → List Nat → Trie) (fun t _ c => .node (some c) t.l t.r)
    (fun _ ih t k c => if k % 2 = 0 then .node t.v (ih t.l (k / 2) c) t.r
      else .node t.v t.l (ih t.r (k / 2) c)) d

theorem insertF_eq : ∀ d t k c, insertF d t k c = Trie.insert d t k c := by
  intro d
  induction d with
  | zero => intro t k c; rfl
  | succ d ih =>
    intro t k c
    show (if k % 2 = 0 then Trie.node t.v (insertF d t.l (k / 2) c) t.r
      else Trie.node t.v t.l (insertF d t.r (k / 2) c)) = _
    simp only [ih, Trie.insert]

noncomputable def nonFalseF (A : Nat) (D : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ ih => if A.testBit (neg x) then ih else x :: ih) D

theorem nonFalseF_eq (A : Nat) : ∀ D, nonFalseF A D = nonFalse A D := by
  intro D
  induction D with
  | nil => rfl
  | cons x xs ih =>
    show (if A.testBit (neg x) then nonFalseF A xs else x :: nonFalseF A xs) = _
    rw [ih]
    unfold nonFalse
    cases h : A.testBit (neg x) <;> simp [List.filter_cons, h]

noncomputable def propagateF (db : Trie) (hs : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun h _ ih A =>
      match findF depth db h with
      | none => false
      | some D =>
        match nonFalseF A D with
        | [] => true
        | [u] => ih (A ||| 2 ^ u)
        | _ :: _ :: _ => false) hs

theorem propagateF_eq (db : Trie) : ∀ hs A, propagateF db hs A = propagate db A hs := by
  intro hs
  induction hs with
  | nil => intro A; rfl
  | cons h hs ih =>
    intro A
    show (match findF depth db h with
      | none => false
      | some D =>
        match nonFalseF A D with
        | [] => true
        | [u] => propagateF db hs (A ||| 2 ^ u)
        | _ :: _ :: _ => false) = _
    rw [findF_eq]
    simp only [propagate]
    split
    · rfl
    · rw [nonFalseF_eq]
      split <;> simp [ih]

noncomputable def initAF (C : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun A => A) (fun x _ ih A => ih (A ||| 2 ^ neg x)) C

theorem initAF_eq : ∀ C A, initAF C A = initA A C := by
  intro C
  induction C with
  | nil => intro A; rfl
  | cons x xs ih => intro A; exact ih _

noncomputable def tokensF (f : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih n => if n = 0 then [] else (n % 1048576) :: ih (n / 1048576)) f

theorem tokensF_eq : ∀ f n, tokensF f n = tokens f n := by
  intro f
  induction f with
  | zero => intro n; rfl
  | succ f ih =>
    intro n
    show (if n = 0 then [] else (n % 1048576) :: tokensF f (n / 1048576)) = _
    simp only [ih, tokens]

noncomputable def decodeStepF (s : Nat) : Nat × List Nat × List Nat :=
  match tokensF 100000 s with
  | i :: k :: rest => (i, rest.take (k - 1), rest.drop (k - 1))
  | _ => (0, [], [])

theorem decodeStepF_eq (s : Nat) : decodeStepF s = decodeStep s := by
  unfold decodeStepF decodeStep; rw [tokensF_eq]

noncomputable def deriveF (ss : List Nat) : Trie → Option Trie :=
  List.rec (motive := fun _ => Trie → Option Trie) (fun db => some db)
    (fun s _ ih db =>
      match decodeStepF s with
      | (i, C, H) => if propagateF db H (initAF C 0) then ih (insertF depth db i C) else none) ss

theorem deriveF_eq : ∀ ss db, deriveF ss db = derive db ss := by
  intro ss
  induction ss with
  | nil => intro db; rfl
  | cons s ss ih =>
    intro db
    show (match decodeStepF s with
      | (i, C, H) => if propagateF db H (initAF C 0) then deriveF ss (insertF depth db i C)
          else none) = _
    rw [decodeStepF_eq, derive]
    generalize decodeStep s = q
    obtain ⟨i, C, H⟩ := q
    simp only [rup, propagateF_eq, initAF_eq, insertF_eq, ih]
    split <;> rename_i h <;> simp [h]

noncomputable def insertAllF (ps : List (Nat × List Nat)) : Trie → Trie :=
  List.rec (motive := fun _ => Trie → Trie) (fun db => db)
    (fun p _ ih db => ih (insertF depth db p.1 p.2)) ps

theorem insertAllF_eq : ∀ ps db, insertAllF ps db = insertAll db ps := by
  intro ps
  induction ps with
  | nil => intro db; rfl
  | cons p ps ih =>
    intro db
    show insertAllF ps (insertF depth db p.1 p.2) = _
    rw [ih, insertF_eq]; rfl

noncomputable def numberF (F : List (List Nat)) : Nat → List (Nat × List Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × List Nat)) (fun _ => [])
    (fun c _ ih i => (i, c) :: ih (i + 1)) F

theorem numberF_eq : ∀ F i, numberF F i = number i F := by
  intro F
  induction F with
  | nil => intro i; rfl
  | cons c cs ih => intro i; show (i, c) :: numberF cs (i + 1) = _; rw [ih]; rfl

noncomputable def allF (p : (Nat × List Nat) → Bool) (l : List (Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => p x && ih) l

theorem allF_eq (p : (Nat × List Nat) → Bool) : ∀ l, allF p l = l.all p := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih => show (p x && allF p xs) = _; rw [ih]; rfl

noncomputable def checkChunkF (F : List (List Nat)) (imports : List (Nat × List Nat))
    (steps : List Nat) (exports : List (Nat × List Nat)) : Bool :=
  match deriveF steps (insertAllF imports (insertAllF (numberF F 1) Trie.leaf)) with
  | none => false
  | some db => allF (fun p => findF depth db p.1 == some p.2) exports

theorem checkChunkF_eq (F imports steps exports) :
    checkChunkF F imports steps exports = checkChunk F imports steps exports := by
  unfold checkChunkF checkChunk
  rw [numberF_eq, insertAllF_eq, insertAllF_eq, deriveF_eq]
  split
  · rfl
  · rw [allF_eq]; simp only [findF_eq]


/-! ## Initial database built in one go (recursion depth `depth`, no chain
of insertions) -/

noncomputable def splitF (ps : List (Nat × List Nat)) : List (Nat × List Nat) × List (Nat × List Nat) :=
  List.rec (motive := fun _ => List (Nat × List Nat) × List (Nat × List Nat)) ([], [])
    (fun p _ ih => if p.1 % 2 = 0 then ((p.1 / 2, p.2) :: ih.1, ih.2)
      else (ih.1, (p.1 / 2, p.2) :: ih.2)) ps

theorem splitF_mem (D : List Nat) : ∀ (ps : List (Nat × List Nat)) (k : Nat),
    ((k, D) ∈ (splitF ps).1 ∨ (k, D) ∈ (splitF ps).2) → ∃ k', (k', D) ∈ ps := by
  intro ps
  induction ps with
  | nil => intro k h; simp [splitF] at h
  | cons p ps ih =>
    intro k h
    have e : splitF (p :: ps) = if p.1 % 2 = 0 then ((p.1 / 2, p.2) :: (splitF ps).1, (splitF ps).2)
      else ((splitF ps).1, (p.1 / 2, p.2) :: (splitF ps).2) := rfl
    rw [e] at h
    split at h
    · simp only [List.mem_cons] at h
      rcases h with (h | h) | h
      · obtain ⟨-, rfl⟩ := Prod.mk.inj h; exact ⟨p.1, by simp⟩
      · obtain ⟨k', hk'⟩ := ih k (Or.inl h); exact ⟨k', by simp [hk']⟩
      · obtain ⟨k', hk'⟩ := ih k (Or.inr h); exact ⟨k', by simp [hk']⟩
    · simp only [List.mem_cons] at h
      rcases h with h | (h | h)
      · obtain ⟨k', hk'⟩ := ih k (Or.inl h); exact ⟨k', by simp [hk']⟩
      · obtain ⟨-, rfl⟩ := Prod.mk.inj h; exact ⟨p.1, by simp⟩
      · obtain ⟨k', hk'⟩ := ih k (Or.inr h); exact ⟨k', by simp [hk']⟩

noncomputable def headVal (ps : List (Nat × List Nat)) : Option (List Nat) :=
  List.rec (motive := fun _ => Option (List Nat)) none (fun p _ _ => some p.2) ps

noncomputable def buildF (d : Nat) : List (Nat × List Nat) → Trie :=
  Nat.rec (motive := fun _ => List (Nat × List Nat) → Trie) (fun ps => .node (headVal ps) .leaf .leaf)
    (fun _ ih ps => .node none (ih (splitF ps).1) (ih (splitF ps).2)) d

theorem buildF_find : ∀ (d : Nat) (ps : List (Nat × List Nat)) (k : Nat) (D : List Nat),
    Trie.find d (buildF d ps) k = some D → ∃ k', (k', D) ∈ ps := by
  intro d
  induction d with
  | zero =>
    intro ps k D h
    cases ps with
    | nil => exact absurd h (by simp [Trie.find, buildF, headVal, Trie.v])
    | cons p ps =>
      have : headVal (p :: ps) = some p.2 := rfl
      simp only [Trie.find, buildF, Trie.v] at h
      rw [this] at h
      cases h; exact ⟨p.1, by simp⟩
  | succ d ih =>
    intro ps k D h
    have e : buildF (d + 1) ps = .node none (buildF d (splitF ps).1) (buildF d (splitF ps).2) := rfl
    rw [e] at h
    simp only [Trie.find, Trie.l, Trie.r] at h
    split at h
    · obtain ⟨k', hk'⟩ := ih _ _ _ h; exact splitF_mem D ps k' (Or.inl hk')
    · obtain ⟨k', hk'⟩ := ih _ _ _ h; exact splitF_mem D ps k' (Or.inr hk')

theorem good_buildF (τ : Nat → Bool) (ps : List (Nat × List Nat))
    (h : ∀ p ∈ ps, clauseT τ p.2 = true) : Good τ (buildF depth ps) := by
  intro k D hD
  obtain ⟨k', hk'⟩ := buildF_find depth ps k D hD
  exact h _ hk'

noncomputable def checkChunkB (F : List (List Nat)) (imports : List (Nat × List Nat))
    (steps : List Nat) (exports : List (Nat × List Nat)) : Bool :=
  match deriveF steps (buildF depth (numberF F 1 ++ imports)) with
  | none => false
  | some db => allF (fun p => findF depth db p.1 == some p.2) exports

theorem chunkB_sound (F : List (List Nat)) (imports : List (Nat × List Nat)) (steps : List Nat)
    (exports : List (Nat × List Nat)) (h : checkChunkB F imports steps exports = true)
    (himp : ∀ p ∈ imports, Entails F p.2) : ∀ p ∈ exports, Entails F p.2 := by
  intro p hp τ hτ
  unfold checkChunkB at h
  split at h
  · exact absurd h (by decide)
  · rename_i db hdb
    rw [deriveF_eq] at hdb
    have g0 : Good τ (buildF depth (numberF F 1 ++ imports)) := by
      apply good_buildF
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · rw [numberF_eq] at hq; exact hτ _ (mem_number F 1 q hq)
      · exact himp q hq τ hτ
    have g2 := derive_sound τ steps _ db g0 hdb
    rw [allF_eq] at h
    have he := List.all_eq_true.mp h p hp
    have hf : Trie.find depth db p.1 = some p.2 := by rw [← findF_eq]; simpa using he
    exact g2 _ _ hf

end LR
