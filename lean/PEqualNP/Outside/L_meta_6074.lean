import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6074

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def sh (n s i : ℕ) : ℕ := if i < n then i else i + s

def mapG (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

def rm (a b : ℕ) (f : Fin a → Fin b) (i : ℕ) : ℕ :=
  if h : i < a then (f ⟨i, h⟩ : ℕ) else b + (i - a)

def mk (C2 C3 : Circuit) (a n : ℕ) (f : Fin a → Fin n) : Circuit :=
  ⟨C2.gates.map (mapG (rm a n f)) ++ C3.gates.map (mapG (sh n C2.size)) ++
    [⟨GateOp.or, [rm a n f C2.output, sh n C2.size C3.output]⟩], n + C2.size + C3.size⟩

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

theorem keyr (a b : ℕ) (f : Fin a → Fin b) (z : Fin b → Bool) (v : List Bool) (i : ℕ) :
    (List.ofFn z ++ v).getD (rm a b f i) false = (List.ofFn (z ∘ f) ++ v).getD i false := by
  unfold rm
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [not_lt] at h
    rw [List.getD_append_right _ v false _ (by simp),
      List.getD_append_right _ v false _ (by simpa using h)]
    congr 1
    simp

theorem fold_map (x y : List Bool) (r : ℕ → ℕ)
    (H : ∀ (v : List Bool) (i : ℕ), (x ++ v).getD (r i) false = (y ++ v).getD i false) :
    ∀ (G : List Gate) (v : List Bool),
    ∃ v' : List Bool, v'.length = v.length + G.length ∧ G.foldl step (y ++ v) = y ++ v' ∧
      (G.map (mapG r)).foldl step (x ++ v) = x ++ v' := by
  intro G
  induction G with
  | nil => intro v; exact ⟨v, by simp, rfl, rfl⟩
  | cons g G ih =>
    intro v
    obtain ⟨v', h1, h2, h3⟩ :=
      ih (v ++ [g.op.eval (g.inputs.map fun i => (y ++ v).getD i false)])
    refine ⟨v', ?_, ?_, ?_⟩
    · simp at h1 ⊢; omega
    · simp only [List.foldl_cons]
      have : step (y ++ v) g =
          y ++ (v ++ [g.op.eval (g.inputs.map fun i => (y ++ v).getD i false)]) := by
        simp [step]
      rw [this]; exact h2
    · simp only [List.foldl_cons, List.map_cons]
      have : step (x ++ v) (mapG r g) =
          x ++ (v ++ [g.op.eval (g.inputs.map fun i => (y ++ v).getD i false)]) := by
        have e : (g.inputs.map r).map (fun i => (x ++ v).getD i false) =
            g.inputs.map fun i => (y ++ v).getD i false := by
          rw [List.map_map]
          apply List.map_congr_left
          intro i _
          exact H v i
        unfold step mapG
        simp only [e]
        simp
      rw [this]; exact h3

theorem core (C2 C3 : Circuit) (a b : ℕ) (f : Fin a → Fin b) (z : Fin b → Bool)
    (h2 : C2.output < a + C2.size) :
    (mk C2 C3 a b f).eval (List.ofFn z) =
      (C2.eval (List.ofFn (z ∘ f)) || C3.eval (List.ofFn z)) := by
  obtain ⟨v2, l2, e2, f2⟩ := fold_map (List.ofFn z) (List.ofFn (z ∘ f)) (rm a b f)
    (keyr a b f z) C2.gates []
  obtain ⟨v3, l3, e3, f3⟩ := fold_map (List.ofFn z ++ v2) (List.ofFn z) (sh b v2.length)
    (fun v i => by simpa using key (List.ofFn z) v2 v i) C3.gates []
  simp only [List.append_nil, List.length_nil, Nat.zero_add] at l2 e2 f2 l3 e3 f3
  have hs : C2.size = v2.length := by unfold Circuit.size; omega
  have hr : rm a b f C2.output < b + v2.length := by
    unfold rm
    split_ifs with h
    · have := (f ⟨C2.output, h⟩).isLt
      omega
    · omega
  have w8 : (mk C2 C3 a b f).wires (List.ofFn z) =
      List.ofFn z ++ v2 ++ v3 ++ [((List.ofFn (z ∘ f) ++ v2).getD C2.output false ||
        (List.ofFn z ++ v3).getD C3.output false)] := by
    rw [wires_eq]
    unfold mk
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [f2, hs, f3]
    unfold step
    have a1 := key (List.ofFn z) v2 v3 C3.output
    have b1 : (List.ofFn z ++ v2 ++ v3).getD (rm a b f C2.output) false =
        (List.ofFn z ++ v2).getD (rm a b f C2.output) false :=
      List.getD_append _ _ _ _ (by simpa using hr)
    have c1 := keyr a b f z v2 C2.output
    simp only [List.length_ofFn] at a1
    simp only [List.map_cons, List.map_nil]
    rw [a1, b1, c1]
    simp [GateOp.eval]
  unfold Circuit.eval
  rw [w8, wires_eq C2, wires_eq C3, e2, e3]
  show (List.ofFn z ++ v2 ++ v3 ++ _).getD (b + C2.size + C3.size) false = _
  rw [List.getD_append_right _ _ _ _ (by simp [Circuit.size]; omega)]
  have : b + C2.size + C3.size - (List.ofFn z ++ v2 ++ v3).length = 0 := by
    simp [Circuit.size]; omega
  rw [this]
  rfl

theorem mono (C2 C3 : Circuit) (a n : ℕ) (f : Fin a → Fin n) (h2 : Monotone2 C2)
    (h3 : Monotone2 C3) : Monotone2 (mk C2 C3 a n f) := by
  intro g hg
  unfold mk at hg
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
  rcases hg with (⟨g', hg', rfl⟩ | ⟨g', hg', rfl⟩) | rfl
  · have := h2 g' hg'
    simpa [mapG] using this
  · have := h3 g' hg'
    simpa [mapG] using this
  · simp

end PEqualNP.Outside.L_meta_6074

theorem PEqualNP.Outside.L_meta_6074 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.Monotone2 x5 → x4.output < x1 + x4.size → x5.output < x2 + x5.size → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x4.size + x5.size + (1 : ℕ) ∧ x10.output < x2 + x10.size ∧ ∀ (x11 : Fin x2 → Bool), x10.eval (List.ofFn x11) = (x4.eval (List.ofFn (x11 ∘ x3)) || x5.eval (List.ofFn x11)) := by
  intro x1 x2 x3 x4 x5 h4 h5 o4 _
  refine ⟨PEqualNP.Outside.L_meta_6074.mk x4 x5 x1 x2 x3,
    PEqualNP.Outside.L_meta_6074.mono x4 x5 x1 x2 x3 h4 h5, ?_, ?_, ?_⟩
  · simp [PEqualNP.Outside.L_meta_6074.mk, PEqualNP.CircuitLowerBounds.Circuit.size]
    omega
  · simp [PEqualNP.Outside.L_meta_6074.mk, PEqualNP.CircuitLowerBounds.Circuit.size]
    omega
  · intro x11
    exact PEqualNP.Outside.L_meta_6074.core x4 x5 x1 x2 x3 x11 o4
