import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8343

open PEqualNP.CircuitLowerBounds

theorem getD_tb (M : List ℕ) (b i : ℕ) :
    (M.getD i 0).testBit b = (M.map fun m => m.testBit b).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases M[i]? <;> simp

theorem main (b : ℕ) (gs : List Gate) :
    ∀ (M : List ℕ), (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
    (List.foldl (fun (x6 : List ℕ) (x7 : Gate) =>
        x6 ++ [if x7.op.eval [Bool.false, Bool.true] = Bool.true
          then x6.getD (x7.inputs.getD 0 0) 0 ||| x6.getD (x7.inputs.getD 1 0) 0
          else x6.getD (x7.inputs.getD 0 0) 0 &&& x6.getD (x7.inputs.getD 1 0) 0]) M gs).map
      (fun m => m.testBit b)
    = gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (M.map fun m => m.testBit b) := by
  induction gs with
  | nil => intro M _; rfl
  | cons g t ih =>
    intro M h
    rw [List.foldl_cons, List.foldl_cons, ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]
    congr 1
    rw [List.map_append]
    congr 1
    obtain ⟨ho, hl⟩ := h g List.mem_cons_self
    obtain ⟨i, j, hij⟩ := List.length_eq_two.mp hl
    rcases ho with ho | ho
    · simp [ho, hij, GateOp.eval, Nat.testBit_and]
      cases M[i]? <;> cases M[j]? <;> simp
    · simp [ho, hij, GateOp.eval, Nat.testBit_or]
      cases M[i]? <;> cases M[j]? <;> simp

end PEqualNP.Outside.L_meta_8343

open PEqualNP.Outside.L_meta_8343 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8343 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ) (x3 x4 : ℕ),   (∀ x5 ∈ x1.gates, (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x5.inputs.length = (2 : ℕ)) →     ((List.foldl                 (fun (x6 : List ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) =>                   have x8 : ℕ := x6.getD (x7.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);                   have x9 : ℕ := x6.getD (x7.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);                   x6 ++ [if x7.op.eval [Bool.false, Bool.true] = Bool.true then x8 ||| x9 else x8 &&& x9])                 x2 x1.gates).getD             x3 (0 : ℕ)).testBit         x4 =       (x1.wires (List.map (fun (x6 : ℕ) => x6.testBit x4) x2)).getD x3 Bool.false := by
  intro C M w b h
  have hm := main b C.gates M h
  rw [getD_tb]
  unfold Circuit.wires
  rw [← hm]
