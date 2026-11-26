import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19442

open PEqualNP.CircuitLowerBounds

deriving instance DecidableEq for GateOp

def c1 : Circuit where
  gates := [
    ⟨GateOp.or, [1, 6]⟩,
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.and, [10, 11]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.or, [12, 14]⟩,
    ⟨GateOp.or, [13, 16]⟩,
    ⟨GateOp.not, [15]⟩,
    ⟨GateOp.and, [17, 18]⟩]
  output := 19

theorem main : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7594810 : ℕ).testBit (5 * u.val + v.val)) C := by
  have hm : ∀ g ∈ c1.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by decide
  refine ⟨c1, fun g hg => ?_, by decide, by decide⟩
  obtain ⟨h1, h2⟩ := hm g hg
  exact ⟨by rcases h1 with h | h | h <;> simp [h], h2⟩

end PEqualNP.Outside.L_meta_19442

theorem PEqualNP.Outside.L_meta_19442 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7594810 : ℕ).testBit (5 * u.val + v.val)) C :=
  PEqualNP.Outside.L_meta_19442.main
