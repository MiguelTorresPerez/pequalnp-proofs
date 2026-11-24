import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5028

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (W : List Bool) (g : Gate) : List Bool :=
  W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]

def run (gs : List Gate) (W : List Bool) : List Bool := gs.foldl step W

lemma run_append (gs : List Gate) (g : Gate) (W : List Bool) :
    run (gs ++ [g]) W = step (run gs W) g := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (W : List Bool) :
    (run gs W).length = W.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_append]; simp [step, ih]; omega

lemma run_gate (d : Gate) (W : List Bool) (gs : List Gate) :
    ∀ j, j < gs.length → (∀ i ∈ (gs.getD j d).inputs, i < W.length + j) →
      (run gs W).getD (W.length + j) false =
        (gs.getD j d).op.eval ((gs.getD j d).inputs.map fun i => (run gs W).getD i false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj hin
    have hl := run_length gs W
    rw [run_append]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e : (gs ++ [g]).getD j d = gs.getD j d := List.getD_append _ _ _ _ h
      rw [e] at hin ⊢
      have h1 := ih j h hin
      unfold step
      rw [List.getD_append _ _ _ _ (by omega), h1]
      congr 1
      apply List.map_congr_left
      intro i hi
      have := hin i hi
      rw [List.getD_append _ _ _ _ (by omega)]
    · have hj' : j = gs.length := by simp at hj; omega
      subst hj'
      have e : (gs ++ [g]).getD gs.length d = g := by simp
      rw [e] at hin ⊢
      unfold step
      rw [← hl]
      have e2 : (run gs W ++ [g.op.eval (g.inputs.map fun i => (run gs W).getD i false)]).getD
          (run gs W).length false = g.op.eval (g.inputs.map fun i => (run gs W).getD i false) := by
        simp
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i hi
      have := hin i hi
      rw [List.getD_append _ _ _ _ (by omega)]

lemma wire_gate (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hrb : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    wireValue C x (n + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wireValue C x i) := by
  have h := run_gate ⟨GateOp.or, []⟩ x C.gates j hj (by
    intro i hi
    rw [hx]
    exact hrb j hj i hi)
  rw [hx] at h
  exact h

lemma wire_or (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hrb : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    wireValue C x (n + j) = true ↔ ∃ i ∈ (gateAt C j).inputs, wireValue C x i = true := by
  rw [wire_gate n C x hx hrb j hj, hop]
  simp [GateOp.eval]

def Leaf (n : ℕ) (C : Circuit) (s : ℕ) : Prop :=
  s < n ∨ (gateAt C (s - n)).op = GateOp.and

lemma list_cover (n : ℕ) (C : Circuit) (w : ℕ)
    (ih : ∀ v < w, ∃ S : Finset ℕ, (∀ s ∈ S, s ≤ v ∧ Leaf n C s) ∧
      ∀ x : Fin n → Bool, wireValue C (List.ofFn x) v = true ↔
        ∃ s ∈ S, wireValue C (List.ofFn x) s = true) :
    ∀ l : List ℕ, (∀ i ∈ l, i < w) → ∃ S : Finset ℕ, (∀ s ∈ S, s < w ∧ Leaf n C s) ∧
      ∀ x : Fin n → Bool, (∃ i ∈ l, wireValue C (List.ofFn x) i = true) ↔
        ∃ s ∈ S, wireValue C (List.ofFn x) s = true := by
  intro l
  induction l with
  | nil => intro _; exact ⟨∅, by simp, by simp⟩
  | cons a l ihl =>
    intro hl
    obtain ⟨S1, hS1, hv1⟩ := ih a (hl a (by simp))
    obtain ⟨S2, hS2, hv2⟩ := ihl (fun i hi => hl i (by simp [hi]))
    have ha := hl a (by simp)
    refine ⟨S1 ∪ S2, ?_, ?_⟩
    · intro s hs
      rcases Finset.mem_union.mp hs with h | h
      · exact ⟨lt_of_le_of_lt (hS1 s h).1 ha, (hS1 s h).2⟩
      · exact hS2 s h
    · intro x
      constructor
      · rintro ⟨i, hi, hval⟩
        rcases List.mem_cons.mp hi with h | h
        · subst h
          obtain ⟨s, hs, hsv⟩ := (hv1 x).mp hval
          exact ⟨s, Finset.mem_union_left _ hs, hsv⟩
        · obtain ⟨s, hs, hsv⟩ := (hv2 x).mp ⟨i, h, hval⟩
          exact ⟨s, Finset.mem_union_right _ hs, hsv⟩
      · rintro ⟨s, hs, hsv⟩
        rcases Finset.mem_union.mp hs with h | h
        · exact ⟨a, by simp, (hv1 x).mpr ⟨s, h, hsv⟩⟩
        · obtain ⟨i, hi, hiv⟩ := (hv2 x).mpr ⟨s, h, hsv⟩
          exact ⟨i, List.mem_cons_of_mem _ hi, hiv⟩

lemma wire_cover (n : ℕ) (C : Circuit) (hm : Monotone2 C) (hrb : ReadsBack n C) :
    ∀ w, w < n + C.gates.length → ∃ S : Finset ℕ, (∀ s ∈ S, s ≤ w ∧ Leaf n C s) ∧
      ∀ x : Fin n → Bool, wireValue C (List.ofFn x) w = true ↔
        ∃ s ∈ S, wireValue C (List.ofFn x) s = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hleaf : Leaf n C w
    · exact ⟨{w}, by simpa using hleaf, by simp⟩
    · have hnw : n ≤ w := by
        by_contra h
        exact hleaf (Or.inl (by omega))
      have hj : w - n < C.gates.length := by omega
      have hmem : gateAt C (w - n) ∈ C.gates := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      have hop : (gateAt C (w - n)).op = GateOp.or := by
        rcases (hm _ hmem).1 with h | h
        · exact absurd (Or.inr h) hleaf
        · exact h
      have hin : ∀ i ∈ (gateAt C (w - n)).inputs, i < w := by
        intro i hi
        have := hrb (w - n) hj i hi
        omega
      obtain ⟨S, hS, hv⟩ := list_cover n C w (fun v hv => ih v hv (by omega)) _ hin
      refine ⟨S, fun s hs => ⟨le_of_lt (hS s hs).1, (hS s hs).2⟩, ?_⟩
      intro x
      rw [← hv x, ← wire_or n C (List.ofFn x) (by simp) hrb (w - n) hj hop]
      have : n + (w - n) = w := by omega
      rw [this]

end PEqualNP.Outside.L_meta_5028

theorem PEqualNP.Outside.L_meta_5028 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x1 ≤ x2.output → x2.output < x1 + x2.size → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - x1)).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∃ (x8 : Finset ℕ), (∀ x9 ∈ x8, x9 < x2.output ∧ (x9 < x1 ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x9 - x1)).op = PEqualNP.CircuitLowerBounds.GateOp.and)) ∧ ∀ (x9 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x9 = Bool.true ↔ ∃ x10 ∈ x8, PEqualNP.CircuitLowerBounds.wireValue x2 (List.ofFn x9) x10 = Bool.true := by
  intro n C hm hrb hle hlt hop
  have hj : C.output - n < C.gates.length := by
    have : C.size = C.gates.length := rfl
    omega
  have hin : ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - n)).inputs,
      i < C.output := by
    intro i hi
    have := hrb (C.output - n) hj i hi
    omega
  obtain ⟨S, hS, hv⟩ := PEqualNP.Outside.L_meta_5028.list_cover n C C.output
    (fun v hv => PEqualNP.Outside.L_meta_5028.wire_cover n C hm hrb v (by
      have : C.size = C.gates.length := rfl
      omega)) _ hin
  refine ⟨S, hS, ?_⟩
  intro x
  rw [← hv x, ← PEqualNP.Outside.L_meta_5028.wire_or n C (List.ofFn x) (by simp) hrb
    (C.output - n) hj hop]
  have : n + (C.output - n) = C.output := by omega
  rw [this]
  rfl
