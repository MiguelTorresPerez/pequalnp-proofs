import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20662

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.or, [3, 10]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.or, [8, 12]⟩,
    ⟨GateOp.and, [5, 11]⟩,
    ⟨GateOp.and, [4, 13]⟩,
    ⟨GateOp.or, [14, 15]⟩], output := 16 }

def monoOk : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

theorem mono_of (C : Circuit)
    (h : (C.gates.all fun g => monoOk g.op && decide (g.inputs.length ≤ 2)) = true) :
    PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  have := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨?_, this.2⟩
  have h1 := this.1
  cases hop : g.op <;> simp_all [monoOk]

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15762432 : ℕ).testBit (5 * u.val + v.val)) 7 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20662

theorem PEqualNP.Outside.L_meta_20662 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15762432 : ℕ).testBit (5 * u.val + v.val)) 7 :=
  PEqualNP.Outside.L_meta_20662.main
