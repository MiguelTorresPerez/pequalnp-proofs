import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19714

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.or, [7, 18]⟩,
    ⟨GateOp.or, [16, 17]⟩,
    ⟨GateOp.or, [2, 21]⟩,
    ⟨GateOp.or, [18, 19]⟩,
    ⟨GateOp.or, [4, 23]⟩,
    ⟨GateOp.or, [3, 5]⟩,
    ⟨GateOp.or, [17, 25]⟩,
    ⟨GateOp.or, [6, 26]⟩,
    ⟨GateOp.or, [6, 16]⟩,
    ⟨GateOp.or, [18, 28]⟩,
    ⟨GateOp.or, [0, 17]⟩,
    ⟨GateOp.or, [19, 30]⟩,
    ⟨GateOp.or, [17, 20]⟩,
    ⟨GateOp.or, [1, 16]⟩,
    ⟨GateOp.or, [19, 33]⟩,
    ⟨GateOp.or, [16, 20]⟩,
    ⟨GateOp.and, [8, 22]⟩,
    ⟨GateOp.and, [9, 24]⟩,
    ⟨GateOp.and, [10, 27]⟩,
    ⟨GateOp.and, [11, 29]⟩,
    ⟨GateOp.and, [12, 31]⟩,
    ⟨GateOp.and, [13, 32]⟩,
    ⟨GateOp.and, [14, 34]⟩,
    ⟨GateOp.and, [15, 35]⟩,
    ⟨GateOp.or, [36, 41]⟩,
    ⟨GateOp.or, [42, 44]⟩,
    ⟨GateOp.or, [43, 45]⟩,
    ⟨GateOp.or, [40, 46]⟩,
    ⟨GateOp.or, [37, 47]⟩,
    ⟨GateOp.or, [39, 48]⟩,
    ⟨GateOp.or, [38, 49]⟩], output := 50 }

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17464622044026729945 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19714

theorem PEqualNP.Outside.L_meta_19714 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17464622044026729945 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  PEqualNP.Outside.L_meta_19714.main
