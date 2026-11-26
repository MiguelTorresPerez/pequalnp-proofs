import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22290

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.or, [5, 10]⟩,
    ⟨GateOp.and, [3, 11]⟩,
    ⟨GateOp.or, [8, 11]⟩,
    ⟨GateOp.or, [1, 7]⟩,
    ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.or, [0, 15]⟩,
    ⟨GateOp.or, [6, 16]⟩,
    ⟨GateOp.or, [10, 14]⟩,
    ⟨GateOp.or, [9, 18]⟩,
    ⟨GateOp.or, [8, 19]⟩,
    ⟨GateOp.and, [17, 20]⟩,
    ⟨GateOp.or, [12, 21]⟩], output := 22 }

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (837113 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22290

theorem PEqualNP.Outside.L_meta_22290 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (837113 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  PEqualNP.Outside.L_meta_22290.main
