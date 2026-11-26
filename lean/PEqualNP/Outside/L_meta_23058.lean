import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23058

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.or, [4, 7]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [9, 12]⟩,
    ⟨GateOp.or, [6, 13]⟩,
    ⟨GateOp.or, [5, 13]⟩,
    ⟨GateOp.or, [4, 11]⟩,
    ⟨GateOp.or, [8, 16]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.and, [0, 14]⟩,
    ⟨GateOp.and, [1, 15]⟩,
    ⟨GateOp.and, [2, 17]⟩,
    ⟨GateOp.and, [3, 18]⟩,
    ⟨GateOp.or, [19, 21]⟩,
    ⟨GateOp.or, [20, 23]⟩,
    ⟨GateOp.or, [22, 24]⟩], output := 25 }

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4030205 : ℕ).testBit (6 * u.val + v.val)) 16 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23058

theorem PEqualNP.Outside.L_meta_23058 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4030205 : ℕ).testBit (6 * u.val + v.val)) 16 :=
  PEqualNP.Outside.L_meta_23058.main
