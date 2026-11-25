import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8409

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def mapG (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

def rm (a b : ℕ) (f : Fin a → Fin b) (i : ℕ) : ℕ :=
  if h : i < a then (f ⟨i, h⟩ : ℕ) else b + (i - a)

def orG (n : ℕ) (p : Fin n × Fin n) : Gate := ⟨GateOp.or, [(p.1 : ℕ), (p.2 : ℕ)]⟩

def mk (a n m : ℕ) (p : Fin m → Fin n × Fin n) (f : Fin a → Fin (n + m)) (C : Circuit) :
    Circuit :=
  ⟨(List.ofFn fun k => orG n (p k)) ++ C.gates.map (mapG (rm a (n + m) f)),
    rm a (n + m) f C.output⟩

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

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

theorem fold_or (n : ℕ) (x : Fin n → Bool) (ps : List (Fin n × Fin n)) : ∀ t : List Bool,
    (ps.map (orG n)).foldl step (List.ofFn x ++ t) =
      List.ofFn x ++ t ++ ps.map (fun p => x p.1 || x p.2) := by
  induction ps with
  | nil => intro t; simp
  | cons p ps ih =>
    intro t
    have h1 : ∀ q : Fin n, (List.ofFn x ++ t).getD (q : ℕ) false = x q := by
      intro q
      rw [List.getD_append _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    have : step (List.ofFn x ++ t) (orG n p) = List.ofFn x ++ (t ++ [x p.1 || x p.2]) := by
      simp only [step, orG, List.map_cons, List.map_nil, h1]
      simp [GateOp.eval]
    simp only [List.map_cons, List.foldl_cons]
    rw [this, ih]
    simp

theorem core (a n m : ℕ) (p : Fin m → Fin n × Fin n) (f : Fin a → Fin (n + m)) (C : Circuit)
    (x : Fin n → Bool) :
    (mk a n m p f C).eval (List.ofFn x) = C.eval (List.ofFn fun i : Fin a =>
      Fin.addCases x (fun k : Fin m => x (p k).1 || x (p k).2) (f i)) := by
  set z : Fin (n + m) → Bool := Fin.append x (fun k : Fin m => x (p k).1 || x (p k).2) with hz
  have hz' : List.ofFn z = List.ofFn x ++ (List.ofFn p).map (fun q => x q.1 || x q.2) := by
    rw [hz, List.ofFn_fin_append, List.map_ofFn]; rfl
  have e0 : (List.ofFn fun k => orG n (p k)) = (List.ofFn p).map (orG n) := by
    rw [List.map_ofFn]; rfl
  obtain ⟨v, _, e2, f2⟩ := fold_map (List.ofFn z) (List.ofFn (z ∘ f)) (rm a (n + m) f)
    (keyr a (n + m) f z) C.gates []
  simp only [List.append_nil] at e2 f2
  have hw : (mk a n m p f C).wires (List.ofFn x) = List.ofFn z ++ v := by
    rw [wires_eq]
    unfold mk
    simp only [List.foldl_append]
    have := fold_or n x (List.ofFn p) []
    simp only [List.append_nil] at this
    rw [e0, this, ← hz', f2]
  have hw2 : C.wires (List.ofFn (z ∘ f)) = List.ofFn (z ∘ f) ++ v := by
    rw [wires_eq, e2]
  show ((mk a n m p f C).wires _).getD (rm a (n + m) f C.output) false =
    (C.wires (List.ofFn (z ∘ f))).getD C.output false
  rw [hw, hw2]
  exact keyr a (n + m) f z v C.output

theorem mono (a n m : ℕ) (p : Fin m → Fin n × Fin n) (f : Fin a → Fin (n + m)) (C : Circuit)
    (h : Monotone2 C) : Monotone2 (mk a n m p f C) := by
  intro g hg
  unfold mk at hg
  simp only [List.mem_append, List.mem_map, List.mem_ofFn] at hg
  rcases hg with ⟨k, rfl⟩ | ⟨g', hg', rfl⟩
  · simp [orG]
  · have := h g' hg'
    simpa [mapG] using this

theorem rb (a n m : ℕ) (p : Fin m → Fin n × Fin n) (f : Fin a → Fin (n + m)) (C : Circuit)
    (h : ReadsBack a C) : ReadsBack n (mk a n m p f C) := by
  intro j hj i hi
  have hl : (mk a n m p f C).gates.length = m + C.gates.length := by simp [mk]
  rw [hl] at hj
  by_cases hjm : j < m
  · have : gateAt (mk a n m p f C) j = orG n (p ⟨j, hjm⟩) := by
      simp [gateAt, mk, List.getElem?_append_left, hjm]
    rw [this] at hi
    simp only [orG, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl
    · have := (p ⟨j, hjm⟩).1.isLt; omega
    · have := (p ⟨j, hjm⟩).2.isLt; omega
  · have hj' : j - m < C.gates.length := by omega
    have : gateAt (mk a n m p f C) j = mapG (rm a (n + m) f) (gateAt C (j - m)) := by
      simp [gateAt, mk, List.getElem?_append_right, not_lt.mp hjm, hj']
    rw [this] at hi
    simp only [mapG, List.mem_map] at hi
    obtain ⟨w, hw, rfl⟩ := hi
    have := h (j - m) hj' w hw
    unfold rm
    split_ifs with hwa
    · have := (f ⟨w, hwa⟩).isLt; omega
    · omega

end PEqualNP.Outside.L_meta_8409

open PEqualNP.Outside.L_meta_8409 in
theorem PEqualNP.Outside.L_meta_8409 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x2 → Fin x1 × Fin x1) (x5 : Fin x3 → Fin (x1 + x2)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x3 x6 → x6.output < x3 + x6.size → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x10 ∧ x10.output < x1 + x10.size ∧ x10.size ≤ x2 + x6.size ∧ ∀ (x11 : Fin x1 → Bool), x10.eval (List.ofFn x11) = x6.eval (List.ofFn fun (x12 : Fin x3) => Fin.addCases x11 (fun (x13 : Fin x2) => x11 (x4 x13).1 || x11 (x4 x13).2) (x5 x12)) := by
  intro x1 x2 x3 x4 x5 x6 hm hr ho
  refine ⟨mk x3 x1 x2 x4 x5 x6, mono _ _ _ _ _ _ hm, rb _ _ _ _ _ _ hr, ?_, ?_, ?_⟩
  · simp only [mk, PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append,
      List.length_ofFn, List.length_map] at ho ⊢
    unfold rm
    split_ifs with h
    · have := (x5 ⟨x6.output, h⟩).isLt; omega
    · omega
  · simp [mk, PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x11
    exact core x3 x1 x2 x4 x5 x6 x11
