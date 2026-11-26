import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22726

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [4, 10]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [7, 14]⟩,
    ⟨GateOp.or, [4, 11]⟩,
    ⟨GateOp.and, [0, 12]⟩,
    ⟨GateOp.and, [1, 13]⟩,
    ⟨GateOp.and, [2, 15]⟩,
    ⟨GateOp.and, [3, 16]⟩,
    ⟨GateOp.or, [18, 19]⟩,
    ⟨GateOp.or, [17, 21]⟩,
    ⟨GateOp.or, [20, 22]⟩], output := 23 }

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883254 : ℕ).testBit (6 * u.val + v.val)) 14 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22726

theorem PEqualNP.Outside.L_meta_22726 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883254 : ℕ).testBit (6 * u.val + v.val)) 14 :=
  PEqualNP.Outside.L_meta_22726.main
