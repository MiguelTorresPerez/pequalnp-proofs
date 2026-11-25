import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7842

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem W_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    W (g :: gs) x = W gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

theorem W_pre (gs : List Gate) (x : List Bool) : ∃ t, W gs x = x ++ t := by
  induction gs generalizing x with
  | nil => exact ⟨[], by simp [W]⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    exact ⟨[_] ++ t, by rw [W_cons, ht, List.append_assoc]⟩

end PEqualNP.Outside.L_meta_7842

open PEqualNP.Outside.L_meta_7842 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7842 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (16 : ℕ) + x1.size → (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (16 : ℕ) + x3 ∧ x7 < (16 : ℕ) + x3) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size ≤ x1.size + (2 : ℕ) ∧ x4.output < (14 : ℕ) + x4.size ∧ (15 : ℕ) < (14 : ℕ) + x4.size ∧ (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (14 : ℕ) + x5 ∧ x9 < (14 : ℕ) + x5) ∧ ∀ (x5 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x5) = x1.eval (List.ofFn x5 ++ [x5 (7 : Fin (14 : ℕ)) || x5 (13 : Fin (14 : ℕ)), x5 (7 : Fin (14 : ℕ)) || x5 (13 : Fin (14 : ℕ)) || x5 (11 : Fin (14 : ℕ))]) ∧ (x4.wires (List.ofFn x5)).getD (15 : ℕ) Bool.false = (x5 (7 : Fin (14 : ℕ)) || x5 (13 : Fin (14 : ℕ)) || x5 (11 : Fin (14 : ℕ))) := by
  intro C hout hok
  refine ⟨⟨⟨GateOp.or, [7, 13]⟩ :: ⟨GateOp.or, [14, 11]⟩ :: C.gates, C.output⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Circuit.size]
  · simp only [Circuit.size, List.length_cons] at hout ⊢; omega
  · simp only [Circuit.size, List.length_cons]; omega
  · intro j g hg
    match j, hg with
    | 0, hg =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst hg
      exact ⟨Or.inr rfl, 7, 13, rfl, by decide, by decide, by decide⟩
    | 1, hg =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hg
      subst hg
      exact ⟨Or.inr rfl, 14, 11, rfl, by decide, by decide, by decide⟩
    | n + 2, hg =>
      simp only [List.getElem?_cons_succ] at hg
      obtain ⟨h1, a, b, h2, h3, h4, h5⟩ := hok n g hg
      exact ⟨h1, a, b, h2, h3, by omega, by omega⟩
  · intro x
    have hL : (List.ofFn x).length = 14 := by simp
    have h7 : (List.ofFn x).getD 7 false = x 7 := by
      simp [List.getD_eq_getElem?_getD]
    have h13 : (List.ofFn x).getD 13 false = x 13 := by
      simp [List.getD_eq_getElem?_getD]
    have h11 : (List.ofFn x).getD 11 false = x 11 := by
      simp [List.getD_eq_getElem?_getD]
    have key : W (⟨GateOp.or, [7, 13]⟩ :: ⟨GateOp.or, [14, 11]⟩ :: C.gates) (List.ofFn x) =
        W C.gates (List.ofFn x ++ [x 7 || x 13, x 7 || x 13 || x 11]) := by
      rw [W_cons, W_cons]
      congr 1
      generalize List.ofFn x = L at hL h7 h13 h11
      have h14 : ∀ a : Bool, (L ++ [a]).getD 14 false = a := by
        intro a; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, hL]
      have h11' : ∀ a : Bool, (L ++ [a]).getD 11 false = x 11 := by
        intro a
        rw [← h11, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega)]
      simp only [List.getD_eq_getElem?_getD] at h7 h13 h11 h14 h11'
      simp [GateOp.eval, h7, h13, h14, h11']
    refine ⟨?_, ?_⟩
    · show (W _ _).getD C.output false = (C.wires _).getD C.output false
      rw [key, wires_eq]
    · show (W _ _).getD 15 false = _
      rw [key]
      obtain ⟨t, ht⟩ := W_pre C.gates (List.ofFn x ++ [x 7 || x 13, x 7 || x 13 || x 11])
      rw [ht]
      generalize List.ofFn x = L at hL
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, List.getElem?_append_right, hL]
