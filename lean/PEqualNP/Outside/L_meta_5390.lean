import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5390

end PEqualNP.Outside.L_meta_5390

theorem PEqualNP.Outside.L_meta_5390 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 18] }], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 8 C ∧ C.size = 12 ∧
  (∀ x : Fin 8 → Bool, PEqualNP.MetaComplexity.circuitFun 8 C x = decide (∃ e ∈ ([(0, 3), (1, 3), (4, 6), (4, 7), (5, 6)] : List (Fin 8 × Fin 8)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 3), (1, 3), (4, 6), (4, 7), (5, 6)] : List (Fin 8 × Fin 8)), PEqualNP.Core.ReadTwiceAt 8 C (C.output - 8) e.1 e.2 ↔ e ∈ ([(0, 3), (4, 6), (4, 7), (5, 6)] : List (Fin 8 × Fin 8))) := by
  rintro C rfl
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩
  intro x
  simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.GateOp.eval, List.ofFn_succ]
  generalize x 0 = a0
  generalize x 1 = a1
  generalize x 2 = a2
  generalize x 3 = a3
  generalize x 4 = a4
  generalize x 5 = a5
  generalize x 6 = a6
  generalize x 7 = a7
  revert a0 a1 a2 a3 a4 a5 a6 a7
  decide +kernel
