import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54445_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 6 → Bool := fun (u : Fin 4) (v : Fin 6) => (323070 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [5, 6] }, { op := GateOp.or, inputs := [10, 7] },
      { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.or, inputs := [10, 12] },
      { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [0, 1] },
      { op := GateOp.or, inputs := [1, 3] }, { op := GateOp.and, inputs := [14, 11] },
      { op := GateOp.and, inputs := [15, 13] }, { op := GateOp.and, inputs := [16, 4] },
      { op := GateOp.or, inputs := [17, 18] }, { op := GateOp.or, inputs := [20, 19] }],
    output := 21 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_54445_aux

theorem PEqualNP.Outside.L_meta_54445 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (323070 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  exact ⟨PEqualNP.Outside.L_meta_54445_aux.upperC, PEqualNP.Outside.L_meta_54445_aux.upper_mono, by decide, PEqualNP.Outside.L_meta_54445_aux.upper_rep⟩
