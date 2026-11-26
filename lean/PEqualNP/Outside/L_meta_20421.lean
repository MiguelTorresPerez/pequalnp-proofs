import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20421

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.and, [1, 5]⟩,
    ⟨GateOp.and, [2, 4]⟩,
    ⟨GateOp.or, [0, 3]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [7, 10]⟩], output := 11 }

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (863 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20421

theorem PEqualNP.Outside.L_meta_20421 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (863 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  PEqualNP.Outside.L_meta_20421.main
