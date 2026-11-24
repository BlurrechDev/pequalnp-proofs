import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4580

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev inc (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

def incB (a b : Fin 26) : Bool :=
  (decide (a.val < 13) && decide (13 ≤ b.val) && decide ((a.val + 26 - b.val) % 13 ∈ [0, 1, 3, 9])) ||
  (decide (b.val < 13) && decide (13 ≤ a.val) && decide ((b.val + 26 - a.val) % 13 ∈ [0, 1, 3, 9]))

def trans (k : Fin 13) (a : Fin 26) : Fin 26 :=
  if a.val < 13 then ⟨(a.val + k.val) % 13, by omega⟩ else ⟨13 + (a.val - 13 + k.val) % 13, by omega⟩

def dual (a : Fin 26) : Fin 26 :=
  if a.val < 13 then ⟨13 + (13 - a.val) % 13, by omega⟩ else ⟨(26 - a.val) % 13, by omega⟩

def mkP (t : List ℕ) (a : Fin 26) : Fin 26 := ⟨t.getD a.val 0 % 26, Nat.mod_lt _ (by norm_num)⟩

def reps : List ℕ := [(8191 : ℕ), (15860 : ℕ), (31200 : ℕ), (107904 : ℕ)]

def Lm (q : Fin 13) (b0 b1 b2 b3 : Bool) (l : Fin 13) : Bool :=
  (b0 && decide (l = q)) || (b1 && decide (l = q - 1)) || (b2 && decide (l = q - 3)) ||
    (b3 && decide (l = q - 9))

def Pm (l : Fin 13) (b0 b1 b2 b3 : Bool) (p : Fin 13) : Bool :=
  (b0 && decide (p = l)) || (b1 && decide (p = l + 1)) || (b2 && decide (p = l + 3)) ||
    (b3 && decide (p = l + 9))

def pmb (L : Fin 13 → Bool) (p : Fin 13) : Bool := decide (∀ l, L l = true → ¬ inc p l)
def lmb (P : Fin 13 → Bool) (l : Fin 13) : Bool := decide (∀ p, P p = true → ¬ inc p l)

def encb (P L : Fin 13 → Bool) : Fin 26 → Bool := fun a => Fin.addCases P L a

def lm (P : Finset (Fin 13)) : Finset (Fin 13) := Finset.univ.filter fun l => ∀ p ∈ P, ¬ inc p l
def pm (L : Finset (Fin 13)) : Finset (Fin 13) := Finset.univ.filter fun p => ∀ l ∈ L, ¬ inc p l

def enc (P L : Finset (Fin 13)) : Fin 26 → Bool :=
  encb (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))

def bidx (b0 b1 b2 b3 : Bool) : ℕ := b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat

def coreT : List (List ℕ) := [
  [1, 0, 2, 3, 8, 5, 7, 6, 4, 9, 12, 11, 10, 13, 25, 15, 20, 18, 17, 19, 16, 21, 22, 24, 23, 14],
  [1, 0, 5, 3, 4, 2, 12, 10, 8, 9, 7, 11, 6, 13, 17, 15, 16, 14, 25, 22, 20, 21, 19, 24, 23, 18],
  [1, 0, 7, 3, 5, 8, 2, 6, 12, 9, 4, 10, 11, 13, 17, 20, 15, 18, 25, 19, 16, 22, 21, 14, 23, 24],
  [1, 5, 0, 6, 4, 10, 12, 2, 9, 8, 7, 11, 3, 18, 17, 23, 16, 14, 22, 25, 19, 21, 20, 24, 15, 13],
  [1, 5, 2, 6, 11, 7, 0, 12, 4, 8, 3, 9, 10, 18, 15, 19, 23, 24, 17, 25, 16, 21, 20, 13, 22, 14],
  [1, 5, 7, 6, 0, 9, 10, 3, 12, 8, 4, 2, 11, 18, 17, 19, 23, 13, 22, 20, 16, 25, 21, 14, 15, 24],
  [2, 4, 0, 1, 5, 3, 6, 11, 12, 10, 7, 9, 8, 14, 17, 13, 18, 15, 16, 23, 24, 22, 20, 19, 21, 25],
  [2, 4, 5, 1, 0, 8, 9, 12, 11, 10, 7, 6, 3, 14, 17, 18, 13, 25, 21, 22, 24, 23, 20, 19, 16, 15],
  [2, 4, 5, 1, 7, 6, 12, 9, 3, 10, 0, 8, 11, 14, 17, 18, 24, 19, 16, 22, 13, 20, 23, 25, 21, 15],
  [3, 0, 2, 1, 8, 10, 6, 7, 11, 9, 12, 4, 5, 13, 25, 14, 18, 20, 23, 19, 24, 21, 22, 16, 17, 15],
  [3, 0, 2, 1, 12, 4, 7, 6, 5, 9, 8, 10, 11, 13, 25, 14, 24, 16, 17, 19, 18, 22, 21, 20, 23, 15],
  [3, 0, 7, 1, 4, 12, 2, 6, 8, 9, 5, 11, 10, 13, 17, 24, 14, 16, 25, 19, 18, 21, 22, 15, 23, 20],
  [3, 7, 0, 8, 4, 12, 11, 6, 1, 10, 5, 2, 9, 20, 17, 25, 21, 16, 24, 23, 18, 14, 22, 15, 19, 13],
  [5, 6, 0, 1, 10, 9, 2, 12, 7, 8, 11, 3, 4, 18, 23, 13, 14, 22, 19, 25, 24, 20, 21, 15, 16, 17],
  [5, 6, 0, 1, 11, 3, 12, 2, 4, 8, 10, 9, 7, 18, 23, 13, 24, 15, 16, 25, 14, 21, 20, 22, 19, 17],
  [5, 6, 7, 1, 2, 11, 10, 3, 0, 8, 9, 12, 4, 18, 19, 24, 14, 15, 23, 20, 13, 25, 21, 22, 16, 17],
  [7, 8, 0, 3, 2, 9, 11, 6, 4, 10, 12, 1, 5, 20, 25, 13, 15, 19, 21, 23, 16, 14, 22, 24, 18, 17]]

def wAL : List (ℕ × ℕ) := [(0, 8191), (7, 15860), (6, 15860), (13, 31200), (0, 15860), (7, 31200), (6, 31200), (1, 107904), (8, 15860), (15, 31200), (14, 31200), (16, 107904), (8, 31200), (2, 107904), (0, 107904), (0, 8191), (0, 8191), (7, 15860), (6, 15860), (13, 31200), (0, 15860), (7, 31200), (6, 31200), (1, 107904), (8, 15860), (15, 31200), (14, 31200), (16, 107904), (8, 31200), (2, 107904), (0, 107904), (0, 8191), (0, 8191), (7, 15860), (6, 15860), (13, 31200), (0, 15860), (7, 31200), (6, 31200), (1, 107904), (8, 15860), (15, 31200), (14, 31200), (16, 107904), (8, 31200), (2, 107904), (0, 107904), (0, 8191), (0, 8191), (7, 15860), (6, 15860), (13, 31200), (0, 15860), (7, 31200), (6, 31200), (1, 107904), (8, 15860), (15, 31200), (14, 31200), (16, 107904), (8, 31200), (2, 107904), (0, 107904), (0, 8191), (0, 8191), (7, 15860), (6, 15860), (13, 31200), (0, 15860), (7, 31200), (6, 31200), (1, 107904), (8, 15860), (15, 31200), (14, 31200), (16, 107904), (8, 31200), (2, 107904), (0, 107904), (0, 8191), (0, 8191), (7, 15860), (6, 15860), (13, 31200), (0, 15860), (7, 31200), (6, 31200), (1, 107904), (8, 15860), (15, 31200), (14, 31200), (16, 107904), (8, 31200), (2, 107904), (0, 107904), (0, 8191), (0, 8191), (7, 15860), (6, 15860), (13, 31200), (0, 15860), (7, 31200), (6, 31200), (1, 107904), (8, 15860), (15, 31200), (14, 31200), (16, 107904), (8, 31200), (2, 107904), (0, 107904), (0, 8191), (0, 8191), (7, 15860), (6, 15860), (13, 31200), (0, 15860), (7, 31200), (6, 31200), (1, 107904), (8, 15860), (15, 31200), (14, 31200), (16, 107904), (8, 31200), (2, 107904), (0, 107904), (0, 8191), (0, 8191), (7, 15860), (6, 15860), (13, 31200), (0, 15860), (7, 31200), (6, 31200), (1, 107904), (8, 15860), (15, 31200), (14, 31200), (16, 107904), (8, 31200), (2, 107904), (0, 107904), (0, 8191), (0, 8191), (7, 15860), (6, 15860), (13, 31200), (0, 15860), (7, 31200), (6, 31200), (1, 107904), (8, 15860), (15, 31200), (14, 31200), (16, 107904), (8, 31200), (2, 107904), (0, 107904), (0, 8191), (0, 8191), (7, 15860), (6, 15860), (13, 31200), (0, 15860), (7, 31200), (6, 31200), (1, 107904), (8, 15860), (15, 31200), (14, 31200), (16, 107904), (8, 31200), (2, 107904), (0, 107904), (0, 8191), (0, 8191), (7, 15860), (6, 15860), (13, 31200), (0, 15860), (7, 31200), (6, 31200), (1, 107904), (8, 15860), (15, 31200), (14, 31200), (16, 107904), (8, 31200), (2, 107904), (0, 107904), (0, 8191), (0, 8191), (7, 15860), (6, 15860), (13, 31200), (0, 15860), (7, 31200), (6, 31200), (1, 107904), (8, 15860), (15, 31200), (14, 31200), (16, 107904), (8, 31200), (2, 107904), (0, 107904), (0, 8191)]

def wBL : List (ℕ × ℕ) := [(0, 8191), (0, 15860), (3, 15860), (0, 31200), (4, 15860), (2, 31200), (4, 31200), (9, 107904), (5, 15860), (1, 31200), (3, 31200), (10, 107904), (5, 31200), (11, 107904), (12, 107904), (0, 8191), (0, 8191), (0, 15860), (3, 15860), (0, 31200), (4, 15860), (2, 31200), (4, 31200), (9, 107904), (5, 15860), (1, 31200), (3, 31200), (10, 107904), (5, 31200), (11, 107904), (12, 107904), (0, 8191), (0, 8191), (0, 15860), (3, 15860), (0, 31200), (4, 15860), (2, 31200), (4, 31200), (9, 107904), (5, 15860), (1, 31200), (3, 31200), (10, 107904), (5, 31200), (11, 107904), (12, 107904), (0, 8191), (0, 8191), (0, 15860), (3, 15860), (0, 31200), (4, 15860), (2, 31200), (4, 31200), (9, 107904), (5, 15860), (1, 31200), (3, 31200), (10, 107904), (5, 31200), (11, 107904), (12, 107904), (0, 8191), (0, 8191), (0, 15860), (3, 15860), (0, 31200), (4, 15860), (2, 31200), (4, 31200), (9, 107904), (5, 15860), (1, 31200), (3, 31200), (10, 107904), (5, 31200), (11, 107904), (12, 107904), (0, 8191), (0, 8191), (0, 15860), (3, 15860), (0, 31200), (4, 15860), (2, 31200), (4, 31200), (9, 107904), (5, 15860), (1, 31200), (3, 31200), (10, 107904), (5, 31200), (11, 107904), (12, 107904), (0, 8191), (0, 8191), (0, 15860), (3, 15860), (0, 31200), (4, 15860), (2, 31200), (4, 31200), (9, 107904), (5, 15860), (1, 31200), (3, 31200), (10, 107904), (5, 31200), (11, 107904), (12, 107904), (0, 8191), (0, 8191), (0, 15860), (3, 15860), (0, 31200), (4, 15860), (2, 31200), (4, 31200), (9, 107904), (5, 15860), (1, 31200), (3, 31200), (10, 107904), (5, 31200), (11, 107904), (12, 107904), (0, 8191), (0, 8191), (0, 15860), (3, 15860), (0, 31200), (4, 15860), (2, 31200), (4, 31200), (9, 107904), (5, 15860), (1, 31200), (3, 31200), (10, 107904), (5, 31200), (11, 107904), (12, 107904), (0, 8191), (0, 8191), (0, 15860), (3, 15860), (0, 31200), (4, 15860), (2, 31200), (4, 31200), (9, 107904), (5, 15860), (1, 31200), (3, 31200), (10, 107904), (5, 31200), (11, 107904), (12, 107904), (0, 8191), (0, 8191), (0, 15860), (3, 15860), (0, 31200), (4, 15860), (2, 31200), (4, 31200), (9, 107904), (5, 15860), (1, 31200), (3, 31200), (10, 107904), (5, 31200), (11, 107904), (12, 107904), (0, 8191), (0, 8191), (0, 15860), (3, 15860), (0, 31200), (4, 15860), (2, 31200), (4, 31200), (9, 107904), (5, 15860), (1, 31200), (3, 31200), (10, 107904), (5, 31200), (11, 107904), (12, 107904), (0, 8191), (0, 8191), (0, 15860), (3, 15860), (0, 31200), (4, 15860), (2, 31200), (4, 31200), (9, 107904), (5, 15860), (1, 31200), (3, 31200), (10, 107904), (5, 31200), (11, 107904), (12, 107904), (0, 8191)]

def wA (q : Fin 13) (b0 b1 b2 b3 : Bool) : ℕ × ℕ := wAL.getD (q.val * 16 + bidx b0 b1 b2 b3) (0, 0)
def wB (l : Fin 13) (b0 b1 b2 b3 : Bool) : ℕ × ℕ := wBL.getD (l.val * 16 + bidx b0 b1 b2 b3) (0, 0)

def IsAut (π : Fin 26 → Fin 26) : Prop :=
  (∀ a b, incB (π a) (π b) = incB a b) ∧ (∀ b, ∃ a, π a = b) ∧
    ((∀ a, (π a).val < 13 ↔ a.val < 13) ∨ (∀ a, (π a).val < 13 ↔ ¬ a.val < 13))

theorem factA : ∀ q : Fin 13, ∀ b0 b1 b2 b3 : Bool, ¬ (b0 = true ∧ b1 = true ∧ b2 = true ∧ b3 = true) →
    (wA q b0 b1 b2 b3).1 < coreT.length ∧ (wA q b0 b1 b2 b3).2 ∈ reps ∧
    ∀ a, encb (pmb (Lm q b0 b1 b2 b3)) (Lm q b0 b1 b2 b3) a = true →
      (wA q b0 b1 b2 b3).2.testBit (mkP (coreT.getD (wA q b0 b1 b2 b3).1 []) (trans (3 - q) a)) = true := by
  decide +kernel

theorem factB : ∀ l : Fin 13, ∀ b0 b1 b2 b3 : Bool, ¬ (b0 = true ∧ b1 = true ∧ b2 = true ∧ b3 = true) →
    (wB l b0 b1 b2 b3).1 < coreT.length ∧ (wB l b0 b1 b2 b3).2 ∈ reps ∧
    ∀ a, encb (Pm l b0 b1 b2 b3) (lmb (Pm l b0 b1 b2 b3)) a = true →
      (wB l b0 b1 b2 b3).2.testBit (mkP (coreT.getD (wB l b0 b1 b2 b3).1 []) (dual (trans (-l) a))) = true := by
  decide +kernel

theorem coreAut : ∀ t ∈ coreT, IsAut (mkP t) := by
  unfold IsAut
  decide +kernel

theorem transAut : ∀ k, IsAut (trans k) := by
  unfold IsAut
  decide +kernel

theorem dualAut : IsAut dual := by
  unfold IsAut
  decide +kernel

-- small facts about the plane, checked by evaluation

theorem hpl_iff : ∀ p l : Fin 13, incB (Fin.castAdd 13 p) (Fin.natAdd 13 l) = true ↔ inc p l := by
  decide

theorem hlp_iff : ∀ p l : Fin 13, incB (Fin.natAdd 13 l) (Fin.castAdd 13 p) = true ↔ inc p l := by
  decide

theorem hpp : ∀ p q : Fin 13, incB (Fin.castAdd 13 p) (Fin.castAdd 13 q) = false := by decide

theorem hll : ∀ l m : Fin 13, incB (Fin.natAdd 13 l) (Fin.natAdd 13 m) = false := by decide

theorem s_pp : ∀ p q : Fin 13,
    ¬ (((Fin.castAdd 13 p : Fin 26) : ℕ) < 13 ↔ ¬ ((Fin.castAdd 13 q : Fin 26) : ℕ) < 13) := by decide

theorem s_ll : ∀ l m : Fin 13,
    ¬ (((Fin.natAdd 13 m : Fin 26) : ℕ) < 13 ↔ ¬ ((Fin.natAdd 13 l : Fin 26) : ℕ) < 13) := by decide

theorem s_pl : ∀ p l : Fin 13,
    (((Fin.natAdd 13 l : Fin 26) : ℕ) < 13 ↔ ¬ ((Fin.castAdd 13 p : Fin 26) : ℕ) < 13) := by decide

theorem s_lp : ∀ p l : Fin 13,
    (((Fin.castAdd 13 p : Fin 26) : ℕ) < 13 ↔ ¬ ((Fin.natAdd 13 l : Fin 26) : ℕ) < 13) := by decide

theorem split26 : ∀ a : Fin 26, (∃ p : Fin 13, a = Fin.castAdd 13 p) ∨ ∃ l : Fin 13, a = Fin.natAdd 13 l := by
  decide

theorem star_cases : ∀ q l : Fin 13, inc q l → l = q ∨ l = q - 1 ∨ l = q - 3 ∨ l = q - 9 := by
  decide

theorem star_cover : ∀ q p : Fin 13, inc p q ∨ inc p (q - 1) ∨ inc p (q - 3) ∨ inc p (q - 9) := by
  decide

theorem off_line : ∀ q : Fin 13, ∃ l : Fin 13, ¬ inc q l := by decide

theorem off_point : ∀ l : Fin 13, ∃ p : Fin 13, ¬ inc p l := by decide

theorem meet : ∀ l m : Fin 13, ∃ p : Fin 13, inc p l ∧ inc p m := by decide

theorem encb_left (P L : Fin 13 → Bool) (p : Fin 13) : encb P L (Fin.castAdd 13 p) = P p := by
  unfold encb; exact Fin.addCases_left p

theorem encb_right (P L : Fin 13 → Bool) (l : Fin 13) : encb P L (Fin.natAdd 13 l) = L l := by
  unfold encb; exact Fin.addCases_right l

theorem enc_left (P L : Finset (Fin 13)) (p : Fin 13) : enc P L (Fin.castAdd 13 p) = decide (p ∈ P) :=
  encb_left _ _ p

theorem enc_right (P L : Finset (Fin 13)) (l : Fin 13) : enc P L (Fin.natAdd 13 l) = decide (l ∈ L) :=
  encb_right _ _ l

def decP (y : Fin 26 → Bool) : Finset (Fin 13) := Finset.univ.filter fun p => y (Fin.castAdd 13 p) = true
def decL (y : Fin 26 → Bool) : Finset (Fin 13) := Finset.univ.filter fun l => y (Fin.natAdd 13 l) = true

theorem enc_dec (y : Fin 26 → Bool) : enc (decP y) (decL y) = y := by
  funext a
  rcases split26 a with ⟨p, rfl⟩ | ⟨l, rfl⟩
  · rw [enc_left]; simp [decP]
  · rw [enc_right]; simp [decL]

theorem getD_mem_of_lt {α : Type} (l : List α) (i : ℕ) (d : α) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

-- the generic maximal false inputs, read on the 26 inputs

def X5 (P L : Finset (Fin 13)) : Prop :=
  (∀ l, l ∈ L ↔ ∀ p ∈ P, ¬ inc p l) ∧ (∀ p ∉ P, ∃ l ∈ L, inc p l) ∧
    (¬ ∃ l, ∀ p ∈ P, inc p l) ∧ ¬ ∃ p, ∀ l ∈ L, inc p l

def X (y : Fin 26 → Bool) : Prop :=
  (∀ a b, y a = true → y b = true → incB a b = false) ∧
  (∀ a, y a = false → ∃ b, y b = true ∧ incB a b = true) ∧
  ¬ ∃ v : Fin 26, ∀ a, y a = true → ((a : ℕ) < 13 ↔ ¬ (v : ℕ) < 13) → incB v a = true

theorem X_to_x5 (y : Fin 26 → Bool) (h : X y) : X5 (decP y) (decL y) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l
    simp only [decL, decP, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hl p hp hi
      have := h1 _ _ hp hl
      rw [(hpl_iff p l).2 hi] at this
      exact Bool.noConfusion this
    · intro hall
      by_contra hl
      have hl' : y (Fin.natAdd 13 l) = false := by simpa using hl
      obtain ⟨b, hb, hib⟩ := h2 _ hl'
      rcases split26 b with ⟨p, rfl⟩ | ⟨m, rfl⟩
      · exact hall p hb ((hlp_iff p l).1 hib)
      · rw [hll] at hib; exact Bool.noConfusion hib
  · intro p hp
    have hp' : y (Fin.castAdd 13 p) = false := by simpa [decP] using hp
    obtain ⟨b, hb, hib⟩ := h2 _ hp'
    rcases split26 b with ⟨q, rfl⟩ | ⟨l, rfl⟩
    · rw [hpp] at hib; exact Bool.noConfusion hib
    · exact ⟨l, by simp only [decL, Finset.mem_filter, Finset.mem_univ, true_and]; exact hb, (hpl_iff p l).1 hib⟩
  · rintro ⟨l, hl⟩
    apply h3
    refine ⟨Fin.natAdd 13 l, ?_⟩
    intro a ha hs
    rcases split26 a with ⟨p, rfl⟩ | ⟨m, rfl⟩
    · exact (hlp_iff p l).2 (hl p (by simp [decP, ha]))
    · exact absurd hs (s_ll l m)
  · rintro ⟨p, hp⟩
    apply h3
    refine ⟨Fin.castAdd 13 p, ?_⟩
    intro a ha hs
    rcases split26 a with ⟨q, rfl⟩ | ⟨l, rfl⟩
    · exact absurd hs (s_pp q p)
    · exact (hpl_iff p l).2 (hp l (by simp only [decL, Finset.mem_filter, Finset.mem_univ, true_and]; exact ha))

theorem x5_to_X (P L : Finset (Fin 13)) (h : X5 P L) : X (enc P L) := by
  obtain ⟨c1, c2, c3, c4⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha hb
    rcases split26 a with ⟨p, rfl⟩ | ⟨l, rfl⟩ <;> rcases split26 b with ⟨q, rfl⟩ | ⟨m, rfl⟩
    · exact hpp p q
    · rw [enc_left] at ha; rw [enc_right] at hb
      simp only [decide_eq_true_eq] at ha hb
      rw [← Bool.not_eq_true]
      intro hi
      exact (c1 m).1 hb p ha ((hpl_iff p m).1 hi)
    · rw [enc_right] at ha; rw [enc_left] at hb
      simp only [decide_eq_true_eq] at ha hb
      rw [← Bool.not_eq_true]
      intro hi
      exact (c1 l).1 ha q hb ((hlp_iff q l).1 hi)
    · exact hll l m
  · intro a ha
    rcases split26 a with ⟨p, rfl⟩ | ⟨l, rfl⟩
    · rw [enc_left] at ha
      simp only [decide_eq_false_iff_not] at ha
      obtain ⟨l, hl, hi⟩ := c2 p ha
      exact ⟨Fin.natAdd 13 l, by rw [enc_right]; simpa using hl, (hpl_iff p l).2 hi⟩
    · rw [enc_right] at ha
      simp only [decide_eq_false_iff_not] at ha
      have : ¬ ∀ p ∈ P, ¬ inc p l := fun h => ha ((c1 l).2 h)
      push_neg at this
      obtain ⟨p, hp, hi⟩ := this
      exact ⟨Fin.castAdd 13 p, by rw [enc_left]; simpa using hp, (hlp_iff p l).2 hi⟩
  · rintro ⟨v, hv⟩
    rcases split26 v with ⟨q, rfl⟩ | ⟨l, rfl⟩
    · apply c4
      refine ⟨q, fun l hl => ?_⟩
      have := hv (Fin.natAdd 13 l) (by rw [enc_right]; simpa using hl) (s_pl q l)
      exact (hpl_iff q l).1 this
    · apply c3
      refine ⟨l, fun p hp => ?_⟩
      have := hv (Fin.castAdd 13 p) (by rw [enc_left]; simpa using hp) (s_lp p l)
      exact (hlp_iff p l).1 this

theorem X_aut (π : Fin 26 → Fin 26) (hπ : IsAut π) (y : Fin 26 → Bool) (hy : X y) : X (y ∘ π) := by
  obtain ⟨hinc, hsurj, hside⟩ := hπ
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha hb
    rw [← hinc]
    exact h1 _ _ ha hb
  · intro a ha
    obtain ⟨b', hb', hab⟩ := h2 _ ha
    obtain ⟨b, rfl⟩ := hsurj b'
    exact ⟨b, hb', by rw [← hinc]; exact hab⟩
  · rintro ⟨v, hv⟩
    apply h3
    refine ⟨π v, ?_⟩
    intro a' ha' hs
    obtain ⟨a, rfl⟩ := hsurj a'
    rw [hinc]
    apply hv a ha'
    rcases hside with h | h
    · rw [h a, h v] at hs; exact hs
    · rw [h a, h v] at hs; tauto

theorem comp_aut {π σ : Fin 26 → Fin 26} (hπ : IsAut π) (hσ : IsAut σ) : IsAut (π ∘ σ) := by
  obtain ⟨i1, s1, d1⟩ := hπ
  obtain ⟨i2, s2, d2⟩ := hσ
  refine ⟨fun a b => by simp only [Function.comp_apply, i1, i2], fun b => ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := s1 b
    obtain ⟨a, rfl⟩ := s2 c
    exact ⟨a, rfl⟩
  · rcases d1 with h1 | h1 <;> rcases d2 with h2 | h2
    · left; intro a; simp only [Function.comp_apply, h1, h2]
    · right; intro a; simp only [Function.comp_apply, h1, h2]
    · right; intro a; simp only [Function.comp_apply, h1, h2]
    · left; intro a; simp only [Function.comp_apply, h1, h2, not_not]

-- relabelling the inputs of a circuit (adapted from L_meta_1351)

def wmap (π : Fin 26 → Fin 26) (w : ℕ) : ℕ := if h : w < 26 then (π ⟨w, h⟩ : ℕ) else w

def relGate (π : Fin 26 → Fin 26) (g : Gate) : Gate := ⟨g.op, g.inputs.map (wmap π)⟩

def relabel (π : Fin 26 → Fin 26) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate π), wmap π C.output⟩

def stepG {α : Type} (E : GateOp → List α → α) (d : α) (w : List α) (g : Gate) : List α :=
  w ++ [E g.op (g.inputs.map fun i => w.getD i d)]

def Rel {α : Type} (π : Fin 26 → Fin 26) (d : α) (W W' : List α) : Prop :=
  26 ≤ W.length ∧ W'.length = W.length ∧ ∀ w : ℕ, W'.getD (wmap π w) d = W.getD w d

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem rel_step {α : Type} (π : Fin 26 → Fin 26) (E : GateOp → List α → α) (d : α)
    (W W' : List α) (g : Gate) (h : Rel π d W W') :
    Rel π d (stepG E d W g) (stepG E d W' (relGate π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : E (relGate π g).op ((relGate π g).inputs.map fun i => W'.getD i d)
      = E g.op (g.inputs.map fun i => W.getD i d) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [stepG]; omega, by simp [stepG]; omega, ?_⟩
  intro w
  simp only [stepG, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold {α : Type} (π : Fin 26 → Fin 26) (E : GateOp → List α → α) (d : α) (gs : List Gate) :
    ∀ W W' : List α, Rel π d W W' →
      Rel π d (gs.foldl (stepG E d) W) ((gs.map (relGate π)).foldl (stepG E d) W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step π E d W W' g h)

theorem fun_relabel (π : Fin 26 → Fin 26) (C : Circuit) (x : Fin 26 → Bool) :
    circuitFun 26 (relabel π C) x = circuitFun 26 C (x ∘ π) := by
  have hinit : Rel π false (List.ofFn (x ∘ π)) (List.ofFn x) := by
    refine ⟨by simp, by simp, ?_⟩
    intro w
    unfold wmap
    split
    · rename_i hw
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
      simp only [List.getElem_ofFn, Function.comp_apply]
    · rename_i hw
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  exact (rel_fold π GateOp.eval false C.gates _ _ hinit).2.2 C.output

def degE (op : GateOp) (l : List ℕ) : ℕ :=
  @ite _ (op = GateOp.and) (lineDegreeGateOpDecEq op GateOp.and) l.sum (l.foldr max 0)

theorem deg_relabel (π : Fin 26 → Fin 26) (C : Circuit) (M M' : Finset ℕ)
    (h : ∀ a : Fin 26, ((π a : ℕ) ∈ M' ↔ (a : ℕ) ∈ M)) :
    (relabel π C).lineDeg 26 M' = C.lineDeg 26 M := by
  have hinit : Rel π 0 ((List.range 26).map fun i => if i ∈ M then 1 else 0)
      ((List.range 26).map fun i => if i ∈ M' then 1 else 0) := by
    refine ⟨by simp, by simp, ?_⟩
    intro w
    unfold wmap
    split
    · rename_i hw
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
      simp only [List.getElem_map, List.getElem_range]
      have := h ⟨w, hw⟩
      simp only at this
      by_cases hm : w ∈ M
      · rw [ite_cond_eq_true _ _ (eq_true hm), ite_cond_eq_true _ _ (eq_true (this.2 hm))]
      · rw [ite_cond_eq_false _ _ (eq_false hm), ite_cond_eq_false _ _ (eq_false (fun h' => hm (this.1 h')))]
    · rename_i hw
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  exact (rel_fold π degE 0 C.gates _ _ hinit).2.2 C.output

-- monotonicity of AND/OR circuits

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ i, f i = true → f' i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hg with hg | hg <;> rw [hg] <;> simp only [GateOp.eval, List.all_map, List.any_map,
    List.all_eq_true, List.any_eq_true, Function.comp_apply, id]
  · intro H i hi; exact h i (H i hi)
  · rintro ⟨i, hi, H⟩; exact ⟨i, hi, h i H⟩

theorem mono_fold (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ W W' : List Bool, W.length = W'.length →
      (∀ i, W.getD i false = true → W'.getD i false = true) →
      ∀ i, (gs.foldl (stepG GateOp.eval false) W).getD i false = true →
        (gs.foldl (stepG GateOp.eval false) W').getD i false = true := by
  induction gs with
  | nil => intro W W' _ h; exact h
  | cons g gs ih =>
    intro W W' hl h
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem g hg'))
    · simp [stepG, hl]
    · intro i hi
      have hv := eval_mono g (hg g (List.mem_cons_self ..)) _ _ h
      simp only [stepG] at hi ⊢
      rcases Nat.lt_trichotomy i W.length with hw | hw | hw
      · rw [List.getD_append _ _ _ _ hw] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · subst hw
        rw [getD_snoc_eq] at hi
        rw [hl, getD_snoc_eq]
        exact hv hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        exact Bool.noConfusion hi

theorem circuitFun_mono (C : Circuit) (hM : Monotone2 C) (x y : Fin 26 → Bool)
    (h : ∀ a, x a = true → y a = true) :
    circuitFun 26 C x = true → circuitFun 26 C y = true := by
  have hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hM g hg).1
    simpa using this
  apply mono_fold C.gates hg _ _ (by simp)
  intro i hi
  by_cases hw : i < 26
  · rw [List.getD_eq_getElem _ _ (by simpa using hw)] at hi ⊢
    simp only [List.getElem_ofFn] at hi ⊢
    exact h _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact Bool.noConfusion hi

theorem mono_relabel (π : Fin 26 → Fin 26) (C : Circuit) (hM : Monotone2 C) :
    Monotone2 (relabel π C) := by
  intro g hg
  simp only [relabel, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have := hM g0 hg0
  simpa [relGate] using this

theorem size_relabel (π : Fin 26 → Fin 26) (C : Circuit) : (relabel π C).size = C.size := by
  simp [relabel, Circuit.size]

-- the three properties of the statement

def X6 (C : Circuit) : Prop :=
  (∀ p l : Fin 13, inc p l → circuitFun 26 C (enc {p} {l}) = true) ∧
    ∀ P L : Finset (Fin 13), X5 P L → circuitFun 26 C (enc P L) = false

def X7 (C : Circuit) : Prop :=
  2 ≤ min (C.lineDeg 26 (Finset.range 13)) (C.lineDeg 26 (Finset.Ico 13 26)) ∧
    3 ≤ max (C.lineDeg 26 (Finset.range 13)) (C.lineDeg 26 (Finset.Ico 13 26))

def X8 (C : Circuit) : Prop := ∃ N ∈ reps, circuitFun 26 C (fun a => N.testBit a) = true

theorem pair_true (C : Circuit) (hM : Monotone2 C) (h6 : X6 C) (π : Fin 26 → Fin 26) (hπ : IsAut π)
    (p l : Fin 13) (hpl : inc p l) : circuitFun 26 C (enc {p} {l} ∘ π) = true := by
  obtain ⟨u, hu⟩ := hπ.2.1 (Fin.castAdd 13 p)
  obtain ⟨w, hw⟩ := hπ.2.1 (Fin.natAdd 13 l)
  have huw : incB u w = true := by rw [← hπ.1 u w, hu, hw]; exact (hpl_iff p l).2 hpl
  have hzu : (enc {p} {l} ∘ π) u = true := by
    show enc {p} {l} (π u) = true
    rw [hu, enc_left]; simp
  have hzw : (enc {p} {l} ∘ π) w = true := by
    show enc {p} {l} (π w) = true
    rw [hw, enc_right]; simp
  rcases split26 u with ⟨p', rfl⟩ | ⟨l', rfl⟩ <;> rcases split26 w with ⟨p'', rfl⟩ | ⟨l'', rfl⟩
  · rw [hpp] at huw; exact Bool.noConfusion huw
  · apply circuitFun_mono C hM _ _ _ (h6.1 p' l'' ((hpl_iff p' l'').1 huw))
    intro a ha
    rcases split26 a with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · rw [enc_left] at ha; simp at ha; subst ha; exact hzu
    · rw [enc_right] at ha; simp at ha; subst ha; exact hzw
  · apply circuitFun_mono C hM _ _ _ (h6.1 p'' l' ((hlp_iff p'' l').1 huw))
    intro a ha
    rcases split26 a with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · rw [enc_left] at ha; simp at ha; subst ha; exact hzw
    · rw [enc_right] at ha; simp at ha; subst ha; exact hzu
  · rw [hll] at huw; exact Bool.noConfusion huw

theorem finish (C : Circuit) (hM : Monotone2 C) (h6 : X6 C) (h7 : X7 C) (π : Fin 26 → Fin 26)
    (hπ : IsAut π) (y : Fin 26 → Bool) (htrue : circuitFun 26 C y = true) (N : ℕ) (hN : N ∈ reps)
    (hcov : ∀ a, y a = true → N.testBit (π a) = true) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size ∧ X6 C' ∧ X7 C' ∧ X8 C' := by
  refine ⟨relabel π C, mono_relabel π C hM, le_of_eq (size_relabel π C), ⟨?_, ?_⟩, ?_, N, hN, ?_⟩
  · intro p l hpl
    rw [fun_relabel]
    exact pair_true C hM h6 π hπ p l hpl
  · intro P L h5
    rw [fun_relabel]
    have hX := X_aut π hπ _ (x5_to_X P L h5)
    have := h6.2 _ _ (X_to_x5 _ hX)
    rwa [enc_dec] at this
  · unfold X7 at h7 ⊢
    rcases hπ.2.2 with hs | hs
    · rw [deg_relabel π C (Finset.range 13) (Finset.range 13) (fun a => by simp [hs a]),
        deg_relabel π C (Finset.Ico 13 26) (Finset.Ico 13 26) (fun a => by
          simp only [Finset.mem_Ico]; have := hs a; have := (π a).2; have := a.2; omega)]
      exact h7
    · rw [deg_relabel π C (Finset.Ico 13 26) (Finset.range 13) (fun a => by
          simp only [Finset.mem_Ico, Finset.mem_range]; have := hs a; have := (π a).2; have := a.2; omega),
        deg_relabel π C (Finset.range 13) (Finset.Ico 13 26) (fun a => by
          simp only [Finset.mem_Ico, Finset.mem_range]; have := hs a; have := (π a).2; have := a.2; omega)]
      obtain ⟨h1, h2⟩ := h7
      exact ⟨by rw [min_comm]; exact h1, by rw [max_comm]; exact h2⟩
  · rw [fun_relabel]
    exact circuitFun_mono C hM _ _ (fun a ha => hcov a ha) htrue

-- the main argument

theorem main (C : Circuit) (hM : Monotone2 C) (h6 : X6 C) (h7 : X7 C)
    (hex : ∃ P L : Finset (Fin 13), (∀ p ∈ P, ∀ l ∈ L, ¬ inc p l) ∧ circuitFun 26 C (enc P L) = true) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size ∧ X6 C' ∧ X7 C' ∧ X8 C' := by
  obtain ⟨P, L, hind, htrue⟩ := hex
  set L1 := lm P with hL1
  set P1 := pm L1 with hP1
  have memL1 : ∀ l, l ∈ L1 ↔ ∀ p ∈ P, ¬ inc p l := by intro l; simp [hL1, lm]
  have memP1 : ∀ p, p ∈ P1 ↔ ∀ l ∈ L1, ¬ inc p l := by intro p; simp [hP1, pm]
  have hPP : P ⊆ P1 := fun p hp => (memP1 p).2 fun l hl => (memL1 l).1 hl p hp
  have hLL : L ⊆ L1 := fun l hl => (memL1 l).2 fun p hp => hind p hp l hl
  have htrue1 : circuitFun 26 C (enc P1 L1) = true := by
    apply circuitFun_mono C hM _ _ _ htrue
    intro a ha
    rcases split26 a with ⟨p, rfl⟩ | ⟨l, rfl⟩
    · rw [enc_left] at ha ⊢; simp only [decide_eq_true_eq] at ha ⊢; exact hPP ha
    · rw [enc_right] at ha ⊢; simp only [decide_eq_true_eq] at ha ⊢; exact hLL ha
  have c1 : ∀ l, l ∈ L1 ↔ ∀ p ∈ P1, ¬ inc p l := by
    intro l
    constructor
    · intro hl p hp; exact (memP1 p).1 hp l hl
    · intro h
      exact (memL1 l).2 fun p hp => h p (hPP hp)
  have c2 : ∀ p ∉ P1, ∃ l ∈ L1, inc p l := by
    intro p hp
    rw [memP1] at hp
    push_neg at hp
    exact hp
  by_cases hA : ∃ q, ∀ l ∈ L1, inc q l
  · obtain ⟨q, hq⟩ := hA
    have key : ∀ l, Lm q (decide (q ∈ L1)) (decide (q - 1 ∈ L1)) (decide (q - 3 ∈ L1))
        (decide (q - 9 ∈ L1)) l = decide (l ∈ L1) := by
      intro l
      rw [Bool.eq_iff_iff, decide_eq_true_eq]
      constructor
      · intro hc
        simp only [Lm, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, or_assoc] at hc
        rcases hc with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> exact h
      · intro hl
        rcases star_cases q l (hq l hl) with rfl | rfl | rfl | rfl <;> simp [Lm, hl]
    have notall : ¬ (decide (q ∈ L1) = true ∧ decide (q - 1 ∈ L1) = true ∧ decide (q - 3 ∈ L1) = true ∧
        decide (q - 9 ∈ L1) = true) := by
      rintro ⟨h0, h1, h2, h3⟩
      simp only [decide_eq_true_eq] at h0 h1 h2 h3
      have hP1e : ∀ p, p ∉ P1 := by
        intro p hp
        rcases star_cover q p with h | h | h | h
        · exact (memP1 p).1 hp _ h0 h
        · exact (memP1 p).1 hp _ h1 h
        · exact (memP1 p).1 hp _ h2 h
        · exact (memP1 p).1 hp _ h3 h
      obtain ⟨l, hl⟩ := off_line q
      exact hl (hq l ((c1 l).2 fun p hp => absurd hp (hP1e p)))
    obtain ⟨hlt, hN, hcov⟩ := factA q _ _ _ _ notall
    have hy : encb (pmb (Lm q (decide (q ∈ L1)) (decide (q - 1 ∈ L1)) (decide (q - 3 ∈ L1))
        (decide (q - 9 ∈ L1)))) (Lm q (decide (q ∈ L1)) (decide (q - 1 ∈ L1)) (decide (q - 3 ∈ L1))
        (decide (q - 9 ∈ L1))) = enc P1 L1 := by
      funext a
      rcases split26 a with ⟨p, rfl⟩ | ⟨l, rfl⟩
      · rw [encb_left, enc_left]
        unfold pmb
        simp only [key, decide_eq_true_eq]
        exact decide_eq_decide.2 (memP1 p).symm
      · rw [encb_right, enc_right, key]
    rw [hy] at hcov
    exact finish C hM h6 h7 _ (comp_aut (coreAut _ (getD_mem_of_lt _ _ _ hlt)) (transAut _))
      _ htrue1 _ hN hcov
  · by_cases hB : ∃ l, ∀ p ∈ P1, inc p l
    · obtain ⟨l, hl⟩ := hB
      have hlmP1 : ∀ m, m ∈ L1 ↔ ∀ p ∈ P1, ¬ inc p m := c1
      have key : ∀ p, Pm l (decide (l ∈ P1)) (decide (l + 1 ∈ P1)) (decide (l + 3 ∈ P1))
          (decide (l + 9 ∈ P1)) p = decide (p ∈ P1) := by
        intro p
        rw [Bool.eq_iff_iff, decide_eq_true_eq]
        constructor
        · intro hc
          simp only [Pm, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, or_assoc] at hc
          rcases hc with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> exact h
        · intro hp
          rcases hl p hp with rfl | rfl | rfl | rfl <;> simp [Pm, hp]
      have notall : ¬ (decide (l ∈ P1) = true ∧ decide (l + 1 ∈ P1) = true ∧ decide (l + 3 ∈ P1) = true ∧
          decide (l + 9 ∈ P1) = true) := by
        rintro ⟨h0, h1, h2, h3⟩
        simp only [decide_eq_true_eq] at h0 h1 h2 h3
        have hon : ∀ p, inc p l → p ∈ P1 := by
          rintro p (rfl | rfl | rfl | rfl) <;> assumption
        have hL1e : ∀ m, m ∉ L1 := by
          intro m hm
          obtain ⟨p, hpl, hpm⟩ := meet l m
          exact (hlmP1 m).1 hm p (hon p hpl) hpm
        obtain ⟨p, hp⟩ := off_point l
        exact hp (hl p ((memP1 p).2 fun m hm => absurd hm (hL1e m)))
      obtain ⟨hlt, hN, hcov⟩ := factB l _ _ _ _ notall
      have hy : encb (Pm l (decide (l ∈ P1)) (decide (l + 1 ∈ P1)) (decide (l + 3 ∈ P1))
          (decide (l + 9 ∈ P1))) (lmb (Pm l (decide (l ∈ P1)) (decide (l + 1 ∈ P1))
          (decide (l + 3 ∈ P1)) (decide (l + 9 ∈ P1)))) = enc P1 L1 := by
        funext a
        rcases split26 a with ⟨p, rfl⟩ | ⟨m, rfl⟩
        · rw [encb_left, enc_left, key]
        · rw [encb_right, enc_right]
          unfold lmb
          simp only [key, decide_eq_true_eq]
          exact decide_eq_decide.2 (hlmP1 m).symm
      rw [hy] at hcov
      exact finish C hM h6 h7 _
        (comp_aut (coreAut _ (getD_mem_of_lt _ _ _ hlt)) (comp_aut dualAut (transAut _)))
        _ htrue1 _ hN hcov
    · exfalso
      have h5 : X5 P1 L1 := ⟨c1, c2, hB, hA⟩
      have := h6.2 P1 L1 h5
      rw [htrue1] at this
      exact Bool.noConfusion this

end PEqualNP.Outside.L_meta_4580

theorem PEqualNP.Outside.L_meta_4580 : let x1 : Type := Fin (13 : ℕ); let x2 : Type := Finset x1; have x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => x3 = x4 ∨ x3 = x4 + (1 : x1) ∨ x3 = x4 + (3 : x1) ∨ x3 = x4 + (9 : x1); have x4 : PEqualNP.CircuitLowerBounds.Circuit → x2 → x2 → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : x2) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x7 : Fin (26 : ℕ)) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x5)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) x7; have x5 : x2 → x2 → Prop := fun (x5 x6 : x2) => (∀ (x7 : x1), x7 ∈ x6 ↔ ∀ x8 ∈ x5, ¬x3 x8 x7) ∧ (∀ x7 ∉ x5, ∃ x9 ∈ x6, x3 x7 x9) ∧ (¬∃ (x7 : x1), ∀ x8 ∈ x5, x3 x8 x7) ∧ ¬∃ (x7 : x1), ∀ x8 ∈ x6, x3 x7 x8; have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x7 x8 : x1), x3 x7 x8 → x4 x6 {x7} {x8} = Bool.true) ∧ ∀ (x7 x8 : x2), x5 x7 x8 → x4 x6 x7 x8 = Bool.false; have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) =>   have x8 : ℕ := x7.lineDeg (26 : ℕ) (Finset.range (13 : ℕ));   have x9 : ℕ := x7.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ));   (2 : ℕ) ≤ Min.min x8 x9 ∧ (3 : ℕ) ≤ Max.max x8 x9; have x8 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ x9 ∈ [(8191 : ℕ), (15860 : ℕ), (31200 : ℕ), (107904 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x8 fun (x10 : Fin (26 : ℕ)) => x9.testBit ↑x10) = Bool.true; ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → x6 x9 → x7 x9 → (∃ (x13 : x2) (x14 : x2), (∀ x15 ∈ x13, ∀ x17 ∈ x14, ¬x3 x15 x17) ∧ x4 x9 x13 x14 = Bool.true) → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x14 ∧ x14.size ≤ x9.size ∧ x6 x14 ∧ x7 x14 ∧ x8 x14 := by
  exact PEqualNP.Outside.L_meta_4580.main
