import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5823

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def sh (n s i : ℕ) : ℕ := if i < n then i else i + s

def shG (n s : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sh n s)⟩

def mk (C2 C3 : Circuit) (n : ℕ) : Circuit :=
  ⟨C2.gates ++ C3.gates.map (shG n C2.size) ++
    [⟨GateOp.or, [C2.output, sh n C2.size C3.output]⟩], n + C2.size + C3.size⟩

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem key (x m v : List Bool) (i : ℕ) :
    (x ++ m ++ v).getD (sh x.length m.length i) false = (x ++ v).getD i false := by
  unfold sh
  split_ifs with h
  · rw [List.append_assoc, List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
  · rw [not_lt] at h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [List.getD_append_right (x ++ m) v false _ (by simp),
      List.getD_append_right x v false _ (by omega)]
    congr 1
    simp
    omega

theorem step_shift (x m v : List Bool) (g : Gate) :
    step (x ++ m ++ v) (shG x.length m.length g) =
      x ++ m ++ (v ++ [g.op.eval (g.inputs.map fun i => (x ++ v).getD i false)]) := by
  have : (g.inputs.map (sh x.length m.length)).map (fun i => (x ++ m ++ v).getD i false) =
      g.inputs.map fun i => (x ++ v).getD i false := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact key x m v i
  unfold step shG
  simp only [this]
  simp

theorem fold_shift (x m : List Bool) : ∀ (G : List Gate) (v : List Bool),
    ∃ v' : List Bool, v'.length = v.length + G.length ∧ G.foldl step (x ++ v) = x ++ v' ∧
      (G.map (shG x.length m.length)).foldl step (x ++ m ++ v) = x ++ m ++ v' := by
  intro G
  induction G with
  | nil => intro v; exact ⟨v, by simp, rfl, rfl⟩
  | cons g G ih =>
    intro v
    obtain ⟨v', h1, h2, h3⟩ :=
      ih (v ++ [g.op.eval (g.inputs.map fun i => (x ++ v).getD i false)])
    refine ⟨v', ?_, ?_, ?_⟩
    · simp at h1 ⊢; omega
    · simp only [List.foldl_cons]
      have : step (x ++ v) g =
          x ++ (v ++ [g.op.eval (g.inputs.map fun i => (x ++ v).getD i false)]) := by
        simp [step]
      rw [this]; exact h2
    · simp only [List.foldl_cons, List.map_cons]
      rw [step_shift]; exact h3

theorem core (C2 C3 : Circuit) (x : List Bool) (h2 : C2.output < x.length + C2.size) :
    (mk C2 C3 x.length).eval x = (C2.eval x || C3.eval x) := by
  obtain ⟨v2, l2, e2, -⟩ := fold_shift x [] C2.gates []
  obtain ⟨v3, l3, e3, f3⟩ := fold_shift x v2 C3.gates []
  simp only [List.append_nil, List.length_nil, Nat.zero_add] at l2 e2 l3 e3 f3
  have hs : C2.size = v2.length := by unfold Circuit.size; omega
  have w8 : (mk C2 C3 x.length).wires x =
      x ++ v2 ++ v3 ++ [((x ++ v2).getD C2.output false || (x ++ v3).getD C3.output false)] := by
    rw [wires_eq]
    unfold mk
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e2, hs, f3]
    unfold step
    have a := key x v2 v3 C3.output
    have b : (x ++ v2 ++ v3).getD C2.output false = (x ++ v2).getD C2.output false :=
      List.getD_append _ _ _ _ (by simp; omega)
    simp only [List.map_cons, List.map_nil]
    rw [a, b]
    simp [GateOp.eval]
  unfold Circuit.eval
  rw [w8, wires_eq C2, wires_eq C3, e2, e3]
  show (x ++ v2 ++ v3 ++ _).getD (x.length + C2.size + C3.size) false = _
  rw [List.getD_append_right _ _ _ _ (by simp [Circuit.size]; omega)]
  have : x.length + C2.size + C3.size - (x ++ v2 ++ v3).length = 0 := by
    simp [Circuit.size]; omega
  rw [this]
  rfl

theorem mono (C2 C3 : Circuit) (n : ℕ) (h2 : Monotone2 C2) (h3 : Monotone2 C3) :
    Monotone2 (mk C2 C3 n) := by
  intro g hg
  unfold mk at hg
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
  rcases hg with (hg | ⟨g', hg', rfl⟩) | rfl
  · exact h2 g hg
  · have := h3 g' hg'
    simpa [shG] using this
  · simp

end PEqualNP.Outside.L_meta_5823

theorem PEqualNP.Outside.L_meta_5823 : ∀ (x1 : ℕ) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.Monotone2 x3 → x2.output < x1 + x1 + x2.size → x3.output < x1 + x1 + x3.size → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.output < x1 + x1 + x8.size ∧ x8.size ≤ x2.size + x3.size + (1 : ℕ) ∧ ∀ (x9 x10 : Fin x1 → Bool), x8.eval (List.ofFn x9 ++ List.ofFn x10) = (x2.eval (List.ofFn x9 ++ List.ofFn x10) || x3.eval (List.ofFn x9 ++ List.ofFn x10)) := by
  intro x1 x2 x3 h2 h3 o2 _
  refine ⟨PEqualNP.Outside.L_meta_5823.mk x2 x3 (x1 + x1),
    PEqualNP.Outside.L_meta_5823.mono x2 x3 _ h2 h3, ?_, ?_, ?_⟩
  · simp [PEqualNP.Outside.L_meta_5823.mk, PEqualNP.CircuitLowerBounds.Circuit.size]
    omega
  · simp [PEqualNP.Outside.L_meta_5823.mk, PEqualNP.CircuitLowerBounds.Circuit.size]
    omega
  · intro x9 x10
    have hl : (List.ofFn x9 ++ List.ofFn x10).length = x1 + x1 := by simp
    have := PEqualNP.Outside.L_meta_5823.core x2 x3 (List.ofFn x9 ++ List.ofFn x10)
      (by rw [hl]; exact o2)
    rw [hl] at this
    exact this
