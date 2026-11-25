import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8734

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem key (n : ℕ) (C : Circuit) (hg : C.gates = []) (x : Fin n → Bool) :
    circuitFun n C x = if h : C.output < n then x ⟨C.output, h⟩ else false := by
  simp only [circuitFun, Circuit.eval, Circuit.wires, hg, List.foldl_nil]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> simp

end PEqualNP.Outside.L_meta_8734

theorem PEqualNP.Outside.L_meta_8734 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x1 ≤ (130 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x5.gates = [] → Fintype.card { x14 : Fin x2 × Fin x2 // x3 x14.1 x14.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x14.1 ∨ x15 = Fin.natAdd x2 x14.2)) = Bool.true } ≤ (44 : ℕ) * x5.size := by
  intro x1 x2 x3 x4 x5 h2 _ _ _ _ _ hrej hg
  have hemp : IsEmpty { x14 : Fin x2 × Fin x2 // x3 x14.1 x14.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x14.1 ∨ x15 = Fin.natAdd x2 x14.2)) = Bool.true } := by
    refine ⟨fun ⟨⟨p, l⟩, _, hacc⟩ => ?_⟩
    rw [PEqualNP.Outside.L_meta_8734.key _ _ hg] at hacc
    by_cases h : x5.output < x2 + x2
    · have hy := hrej (fun j => decide (j = ⟨x5.output, h⟩)) ?_ ?_
      · rw [PEqualNP.Outside.L_meta_8734.key _ _ hg] at hy
        simp [h] at hy
      · refine le_trans ?_ (le_trans (by norm_num : 1 ≤ 2) h2)
        rw [Fintype.card_le_one_iff_subsingleton]
        refine ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => ?_⟩
        simp only [decide_eq_true_eq] at ha hb
        have := ha.trans hb.symm
        simp only [Fin.natAdd_inj] at this
        exact Subtype.ext this
      · rintro ⟨a, b, _, ha, hb⟩
        simp only [decide_eq_true_eq] at ha hb
        have := congrArg Fin.val (ha.trans hb.symm)
        simp at this
        omega
    · simp [h] at hacc
  rw [Fintype.card_eq_zero]
  exact Nat.zero_le _
