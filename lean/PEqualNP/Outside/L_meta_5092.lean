import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5092

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A 13 gate circuit for the edge function, built from the vertex cover 1, 2, 4, 7:
-- (x1 and (x0 or x2 or x5)) or (x2 and (x3 or x6)) or (x4 and (x0 or x6 or x7)) or (x7 and (x3 or x5)).
def C : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [1, 9]⟩,
    ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [2, 11]⟩,
    ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [13, 7]⟩, ⟨GateOp.and, [4, 14]⟩,
    ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [7, 16]⟩,
    ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [18, 15]⟩, ⟨GateOp.or, [19, 17]⟩], 20⟩

theorem fanin : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem size_le : C.size ≤ 14 := by decide

theorem computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) =
    (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 ||
      x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) := by
  decide +kernel

end PEqualNP.Outside.L_meta_5092

-- A refutation: the statement is false, since the circuit above has 13 gates and computes the
-- edge function exactly.
theorem PEqualNP.Outside.L_meta_5092 : ¬ (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → ∃ (x4 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x4) ≠ (x4 (0 : Fin (8 : ℕ)) && x4 (1 : Fin (8 : ℕ)) || x4 (1 : Fin (8 : ℕ)) && x4 (2 : Fin (8 : ℕ)) || x4 (2 : Fin (8 : ℕ)) && x4 (3 : Fin (8 : ℕ)) || x4 (0 : Fin (8 : ℕ)) && x4 (4 : Fin (8 : ℕ)) || x4 (1 : Fin (8 : ℕ)) && x4 (5 : Fin (8 : ℕ)) || x4 (2 : Fin (8 : ℕ)) && x4 (6 : Fin (8 : ℕ)) || x4 (3 : Fin (8 : ℕ)) && x4 (7 : Fin (8 : ℕ)) || x4 (4 : Fin (8 : ℕ)) && x4 (6 : Fin (8 : ℕ)) || x4 (5 : Fin (8 : ℕ)) && x4 (7 : Fin (8 : ℕ)) || x4 (7 : Fin (8 : ℕ)) && x4 (4 : Fin (8 : ℕ)))) := by
  intro h
  obtain ⟨x, hx⟩ := h PEqualNP.Outside.L_meta_5092.C PEqualNP.Outside.L_meta_5092.fanin
    PEqualNP.Outside.L_meta_5092.size_le
  exact hx (PEqualNP.Outside.L_meta_5092.computes x)
