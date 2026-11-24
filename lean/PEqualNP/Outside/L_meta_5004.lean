import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5004

open PEqualNP.CircuitLowerBounds

/-- Rename every wire a gate reads. -/
def relabelGate (s : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map s⟩

/-- The invariant of the fold: the renamed wire list read at `s i` is the original read at `i`. -/
theorem fold_inv (n : ℕ) (s : ℕ → ℕ) (h1 : ∀ i < n, s i < n) (h2 : ∀ i, n ≤ i → s i = i)
    (gs : List Gate) : ∀ (w' w : List Bool), w'.length = w.length → n ≤ w.length →
      (∀ i, w'.getD (s i) false = w.getD i false) →
      ∀ i, ((gs.map (relabelGate s)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD (s i) false
        = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
            i false := by
  induction gs with
  | nil => intro w' w _ _ h i; exact h i
  | cons g gs ih =>
    intro w' w hl hn h
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [hl]
    · simp; omega
    · have hv : (relabelGate s g).op.eval
          ((relabelGate s g).inputs.map fun i => w'.getD i false)
          = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [relabelGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact h a
      rw [hv]
      intro i
      have hi := h i
      simp only [List.getD_eq_getElem?_getD] at hi ⊢
      rcases Nat.lt_or_ge i w.length with hlt | hge
      · have hs : s i < w'.length := by
          rcases Nat.lt_or_ge i n with a | a
          · have := h1 i a; omega
          · rw [h2 i a]; omega
        rw [List.getElem?_append_left hs, List.getElem?_append_left hlt]
        exact hi
      · have hs : s i = i := h2 i (by omega)
        rw [hs, List.getElem?_append_right (by omega), List.getElem?_append_right hge, hl]

end PEqualNP.Outside.L_meta_5004

theorem PEqualNP.Outside.L_meta_5004 : ∀ (x1 : ℕ) (x2 : ℕ → ℕ), (∀ x3 < x1, x2 x3 < x1) → (∀ (x4 : ℕ), x1 ≤ x4 → x2 x4 = x4) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size = x5.size ∧ ∀ (x8 x9 : List Bool), x8.length = x1 → x9.length = x1 → (∀ (x12 : ℕ), x8.getD (x2 x12) Bool.false = x9.getD x12 Bool.false) → x7.eval x8 = x5.eval x9 := by
  intro n s h1 h2 C hC
  refine ⟨⟨C.gates.map (PEqualNP.Outside.L_meta_5004.relabelGate s), s C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := hC g0 hg0
    simpa [PEqualNP.Outside.L_meta_5004.relabelGate] using this
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x y hx hy h
    exact PEqualNP.Outside.L_meta_5004.fold_inv n s h1 h2 C.gates x y (by omega) (by omega) h
      C.output
