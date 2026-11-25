import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8047

open PEqualNP.CircuitLowerBounds

theorem getD_tb (M : List ℕ) (b i : ℕ) :
    (M.getD i 0).testBit b = (M.map fun m => m.testBit b).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases M[i]? <;> simp

theorem tb_or (b : ℕ) (l : List ℕ) :
    (List.foldr (fun (x7 x8 : ℕ) => x7 ||| x8) 0 l).testBit b
      = (l.map fun m => m.testBit b).any id := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.foldr_cons, Nat.testBit_or, ih]

theorem tb_and (n b : ℕ) (hb : b < n) (l : List ℕ) :
    (List.foldr (fun (x7 x8 : ℕ) => x7 &&& x8) (2 ^ n - 1) l).testBit b
      = (l.map fun m => m.testBit b).all id := by
  induction l with
  | nil => simp [Nat.testBit_two_pow_sub_one, hb]
  | cons a t ih => simp [List.foldr_cons, Nat.testBit_and, ih]

theorem main (n b : ℕ) (hb : b < n) (gs : List Gate) :
    ∀ (M : List ℕ), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (List.foldl (fun (x5 : List ℕ) (x6 : Gate) => x5 ++ [if x6.op.eval [Bool.true, Bool.false] = Bool.true then List.foldr (fun (x7 x8 : ℕ) => x7 ||| x8) (0 : ℕ) (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs) else List.foldr (fun (x7 x8 : ℕ) => x7 &&& x8) ((2 : ℕ) ^ n - (1 : ℕ)) (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs)]) M gs).map (fun m => m.testBit b)
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
    rcases h g List.mem_cons_self with ho | ho
    · simp [ho, GateOp.eval, tb_and n b hb, List.map_map, Function.comp_def]
      congr 1; funext i; cases M[i]? <;> simp
    · simp [ho, GateOp.eval, tb_or, List.map_map, Function.comp_def]
      congr 1; funext i; cases M[i]? <;> simp

end PEqualNP.Outside.L_meta_8047

open PEqualNP.Outside.L_meta_8047 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8047 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     have x5 : List ℕ := List.foldl (fun (x5 : List ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) => x5 ++ [if x6.op.eval [Bool.true, Bool.false] = Bool.true then List.foldr (fun (x7 x8 : ℕ) => x7 ||| x8) (0 : ℕ) (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs) else List.foldr (fun (x7 x8 : ℕ) => x7 &&& x8) ((2 : ℕ) ^ x1 - (1 : ℕ)) (List.map (fun (x7 : ℕ) => x5.getD x7 (0 : ℕ)) x6.inputs)]) x3 x2.gates;     ∀ x6 < x1, (x5.getD x2.output (0 : ℕ)).testBit x6 = x2.eval (List.map (fun (x8 : ℕ) => x8.testBit x6) x3) := by
  intro n C M hm x5 b hb
  have h := main n b hb C.gates M (fun g hg => by
    have := (hm g hg).1
    simpa [Set.mem_insert_iff] using this)
  rw [getD_tb]
  show _ = (C.wires _).getD C.output false
  unfold Circuit.wires
  rw [← h]
