import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20877

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.and, [5, 10]⟩,
    ⟨GateOp.and, [11, 12]⟩,
    ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.or, [16, 17]⟩,
    ⟨GateOp.or, [15, 18]⟩], output := 19 }

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32249889 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20877

theorem PEqualNP.Outside.L_meta_20877 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (32249889 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_20877.main
