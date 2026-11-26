import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22772

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.or, [3, 7]⟩,
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [5, 11]⟩,
    ⟨GateOp.and, [2, 12]⟩,
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.and, [14, 15]⟩,
    ⟨GateOp.or, [6, 16]⟩,
    ⟨GateOp.or, [1, 17]⟩,
    ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.or, [14, 19]⟩,
    ⟨GateOp.and, [18, 20]⟩,
    ⟨GateOp.or, [13, 21]⟩,
    ⟨GateOp.or, [4, 22]⟩], output := 23 }

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948413 : ℕ).testBit (6 * u.val + v.val)) 14 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22772

theorem PEqualNP.Outside.L_meta_22772 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948413 : ℕ).testBit (6 * u.val + v.val)) 14 :=
  PEqualNP.Outside.L_meta_22772.main
