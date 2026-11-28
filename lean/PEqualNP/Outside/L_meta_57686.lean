import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_57686.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.or, [13, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_57686.Helpers

theorem PEqualNP.Outside.L_meta_57686 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270716733 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_57686.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_57686.Helpers.witness]
