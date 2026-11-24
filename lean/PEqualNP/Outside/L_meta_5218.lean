import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5218

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

lemma run_high (gs : List Gate) (W : List Bool) (i : ℕ) (h : W.length + gs.length ≤ i) :
    (run gs W).getD i false = false :=
  List.getD_eq_default _ _ (by rw [run_length]; exact h)

lemma step_low (W : List Bool) (g : Gate) (i : ℕ) (h : i < W.length) :
    (step W g).getD i false = W.getD i false := by
  unfold step
  rw [List.getD_append _ _ _ _ h]

lemma step_top (W : List Bool) (g : Gate) :
    (step W g).getD W.length false = g.op.eval (g.inputs.map fun i => W.getD i false) := by
  unfold step
  simp

lemma run_low (gs : List Gate) (W : List Bool) (i : ℕ) (h : i < W.length) :
    (run gs W).getD i false = W.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_append, step_low _ _ _ (by rw [run_length]; omega), ih]

lemma run_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (W W' : List Bool) (hl : W.length = W'.length)
    (h : ∀ i, W.getD i false = true → W'.getD i false = true) :
    ∀ i, (run gs W).getD i false = true → (run gs W').getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa [run] using h
  | append_singleton gs g ih =>
    have ih' := ih (fun g hg => hm g (by simp [hg]))
    have l1 := run_length gs W
    have l2 := run_length gs W'
    intro i hi
    rw [run_append] at hi ⊢
    rcases Nat.lt_trichotomy i (run gs W).length with hlt | heq | hgt
    · rw [step_low _ _ _ hlt] at hi
      rw [step_low _ _ _ (by omega)]
      exact ih' i hi
    · have e : i = (run gs W').length := by omega
      rw [heq, step_top] at hi
      rw [e, step_top]
      rcases hm g (by simp) with hop | hop
      · rw [hop] at hi ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi ⊢
        intro u hu
        exact ih' u (hi u hu)
      · rw [hop] at hi ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi ⊢
        obtain ⟨u, hu, hv⟩ := hi
        exact ⟨u, hu, ih' u hv⟩
    · rw [List.getD_eq_default _ _ (by simp [step]; omega)] at hi
      exact Bool.noConfusion hi

lemma run_diff (d : Gate) (gs : List Gate) (W W' : List Bool) (hl : W.length = W'.length) :
    ∀ j, j < gs.length →
      (run gs W).getD (W.length + j) false ≠ (run gs W').getD (W.length + j) false →
      ∃ u ∈ (gs.getD j d).inputs, u < W.length + j ∧
        (run gs W).getD u false ≠ (run gs W').getD u false := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    have l1 := run_length gs W
    have l2 := run_length gs W'
    intro j hj hne
    rw [run_append, run_append] at hne ⊢
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e : (gs ++ [g]).getD j d = gs.getD j d := List.getD_append _ _ _ _ h
      rw [e]
      rw [step_low _ _ _ (by omega), step_low _ _ _ (by omega)] at hne
      obtain ⟨u, hu, hlt, hd⟩ := ih j h hne
      refine ⟨u, hu, hlt, ?_⟩
      rw [step_low _ _ _ (by omega), step_low _ _ _ (by omega)]
      exact hd
    · have hj' : j = gs.length := by simp at hj; omega
      subst hj'
      have e : (gs ++ [g]).getD gs.length d = g := by simp
      rw [e]
      have e1 : W.length + gs.length = (run gs W).length := by omega
      have e2 : W.length + gs.length = (run gs W').length := by omega
      by_contra hcon
      push Not at hcon
      apply hne
      rw [show (step (run gs W) g).getD (W.length + gs.length) false =
        (step (run gs W) g).getD (run gs W).length false by rw [e1], step_top]
      rw [show (step (run gs W') g).getD (W.length + gs.length) false =
        (step (run gs W') g).getD (run gs W').length false by rw [e2], step_top]
      congr 1
      apply List.map_congr_left
      intro u hu
      by_cases hlt : u < W.length + gs.length
      · have := hcon u hu hlt
        rw [step_low _ _ _ (by omega), step_low _ _ _ (by omega)] at this
        exact this
      · rw [run_high _ _ _ (by omega), run_high _ _ _ (by omega)]

lemma getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run C.gates (List.ofFn x)).getD w false

def Diff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (v : Fin n) (w : ℕ) : Prop :=
  wv n C x w ≠ wv n C (Function.update x v false) w

def R (n : ℕ) (C : Circuit) (x : Fin n → Bool) (v : Fin n) (a b : ℕ) : Prop :=
  Diff n C x v b ∧ ∃ j, j < C.gates.length ∧ a = n + j ∧
    b ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs

def Live (n : ℕ) (C : Circuit) (x : Fin n → Bool) (v : Fin n) (w : ℕ) : Prop :=
  Diff n C x v C.output ∧ Relation.ReflTransGen (R n C x v) C.output w

lemma live_diff {n : ℕ} {C : Circuit} {x : Fin n → Bool} {v : Fin n} {w : ℕ}
    (h : Live n C x v w) : Diff n C x v w := by
  obtain ⟨ho, hr⟩ := h
  cases hr with
  | refl => exact ho
  | tail _ hab => exact hab.1

lemma live_parent {n : ℕ} {C : Circuit} {x : Fin n → Bool} {v : Fin n} {w : ℕ}
    (h : Live n C x v w) (hw : w ≠ C.output) :
    ∃ j, j < C.gates.length ∧ Live n C x v (n + j) ∧
      w ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs := by
  obtain ⟨ho, hr⟩ := h
  cases hr with
  | refl => exact absurd rfl hw
  | tail hab hR =>
    obtain ⟨_, j, hj, rfl, hmem⟩ := hR
    exact ⟨j, hj, ⟨ho, hab⟩, hmem⟩

lemma live_var {n : ℕ} {C : Circuit} {x : Fin n → Bool} {v : Fin n} :
    ∀ w, Live n C x v w → Live n C x v v.val := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hL
    have hd := live_diff hL
    by_cases hw : w < n
    · unfold Diff wv at hd
      rw [run_low _ _ _ (by simpa using hw), run_low _ _ _ (by simpa using hw),
        getD_ofFn _ _ hw, getD_ofFn _ _ hw] at hd
      have hv : (⟨w, hw⟩ : Fin n) = v := by
        by_contra hne
        exact hd (Function.update_of_ne hne _ _).symm
      have : w = v.val := by rw [← hv]
      rw [← this]
      exact hL
    · have hj : w - n < C.gates.length := by
        by_contra hge
        apply hd
        unfold wv
        rw [run_high _ _ _ (by simp; omega), run_high _ _ _ (by simp; omega)]
      have hd' := hd
      unfold Diff wv at hd'
      have hwe : w = (List.ofFn x).length + (w - n) := by simp; omega
      rw [hwe] at hd'
      obtain ⟨u, hu, hlt, hdu⟩ := run_diff ⟨GateOp.or, []⟩ C.gates (List.ofFn x)
        (List.ofFn (Function.update x v false)) (by simp) (w - n) hj hd'
      have hlt' : u < w := by simp at hlt; omega
      exact ih u hlt' ⟨hL.1, hL.2.tail ⟨hdu, w - n, hj, by omega, hu⟩⟩

lemma count (X D : Finset ℕ) (o : ℕ) (ins : ℕ → List ℕ)
    (hlen : ∀ h ∈ D, (ins h).length ≤ 2)
    (hpar : ∀ x ∈ X, x ≠ o → ∃ h ∈ D, x ∈ ins h) : X.card ≤ 2 * D.card + 1 := by
  have hsub : X.erase o ⊆ D.biUnion (fun h => (ins h).toFinset) := by
    intro x hx
    rw [Finset.mem_erase] at hx
    obtain ⟨h, hD, hmem⟩ := hpar x hx.2 hx.1
    rw [Finset.mem_biUnion]
    exact ⟨h, hD, by simpa using hmem⟩
  have h1 : (D.biUnion (fun h => (ins h).toFinset)).card ≤ D.card * 2 := by
    refine le_trans Finset.card_biUnion_le ?_
    have := Finset.sum_le_card_nsmul D (fun h => ((ins h).toFinset).card) 2
      (fun h hD => le_trans (List.toFinset_card_le _) (hlen h hD))
    simpa using this
  have h2 := Finset.card_le_card hsub
  have h3 := Finset.pred_card_le_card_erase (s := X) (a := o)
  omega

end PEqualNP.Outside.L_meta_5218

theorem PEqualNP.Outside.L_meta_5218 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1 → Bool)) (x4 : Finset (Fin x1)), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ x6 ∈ x4, ∃ x8 ∈ x3, PEqualNP.MetaComplexity.circuitFun x1 x2 x8 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x8 x6 Bool.false)) → x4.card ≤ Fintype.card { x7 : Fin x2.size // (x2.wires (List.replicate x1 Bool.false)).getD (x1 + ↑x7) Bool.false = Bool.false ∧ ∃ x8 ∈ x3, PEqualNP.EdgeOwnership.gateVal x1 x2 (↑x7) x8 = Bool.true } + (1 : ℕ) := by
  intro n C A V hM hV
  classical
  have hsize : C.size = C.gates.length := rfl
  have hm : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g hg => (hM g hg).1
  let D : Finset ℕ := (Finset.range C.gates.length).filter
    (fun j => ∃ x ∈ A, ∃ v ∈ V, PEqualNP.Outside.L_meta_5218.Live n C x v (n + j))
  let D' : Finset ℕ := D.image (fun j => n + j)
  let X : Finset ℕ := V.image (fun v => v.val) ∪ D'
  have hD'card : D'.card = D.card :=
    Finset.card_image_of_injective _ (add_right_injective n)
  have hXcard : X.card = V.card + D.card := by
    rw [← hD'card, ← Finset.card_image_of_injective V Fin.val_injective]
    apply Finset.card_union_of_disjoint
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
    have := v.isLt
    omega
  have hlive : ∀ x ∈ A, ∀ v ∈ V, ∀ w, PEqualNP.Outside.L_meta_5218.Live n C x v w →
      w ≠ C.output → ∃ h ∈ D', w ∈ (C.gates.getD (h - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs := by
    intro x hx v hv w hL hw
    obtain ⟨j, hj, hLj, hmem⟩ := PEqualNP.Outside.L_meta_5218.live_parent hL hw
    refine ⟨n + j, ?_, ?_⟩
    · simp only [D', D, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      exact ⟨j, ⟨hj, x, hx, v, hv, hLj⟩, rfl⟩
    · have : n + j - n = j := by omega
      rw [this]
      exact hmem
  have hcount := PEqualNP.Outside.L_meta_5218.count X D' C.output
    (fun h => (C.gates.getD (h - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs)
    (by
      intro h hh
      simp only [D', D, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hh
      obtain ⟨j, ⟨hj, _⟩, rfl⟩ := hh
      have e : n + j - n = j := by omega
      simp only [e]
      rw [List.getD_eq_getElem _ _ hj]
      exact (hM _ (List.getElem_mem hj)).2)
    (by
      intro w hw hne
      have hw' : w ∈ V.image (fun v => v.val) ∨ w ∈ D' := Finset.mem_union.mp hw
      rcases hw' with hw | hw
      · rw [Finset.mem_image] at hw
        obtain ⟨v, hv, rfl⟩ := hw
        obtain ⟨x, hx, hdiff⟩ := hV v hv
        have hL0 : PEqualNP.Outside.L_meta_5218.Live n C x v C.output :=
          ⟨hdiff, Relation.ReflTransGen.refl⟩
        exact hlive x hx v hv _ (PEqualNP.Outside.L_meta_5218.live_var _ hL0) hne
      · simp only [D', D, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hw
        obtain ⟨j, ⟨_, x, hx, v, hv, hL⟩, rfl⟩ := hw
        exact hlive x hx v hv _ hL hne)
  have hDle : D.card ≤ Fintype.card { x7 : Fin C.size //
      (C.wires (List.replicate n Bool.false)).getD (n + ↑x7) Bool.false = Bool.false ∧
      ∃ x8 ∈ A, PEqualNP.EdgeOwnership.gateVal n C (↑x7) x8 = Bool.true } := by
    have hP : ∀ j ∈ D, j < C.size ∧
        (C.wires (List.replicate n Bool.false)).getD (n + j) Bool.false = Bool.false ∧
        ∃ x8 ∈ A, PEqualNP.EdgeOwnership.gateVal n C j x8 = Bool.true := by
      intro j hj
      simp only [D, Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨hjl, x, hx, v, hv, hL⟩ := hj
      have hd := PEqualNP.Outside.L_meta_5218.live_diff hL
      unfold PEqualNP.Outside.L_meta_5218.Diff PEqualNP.Outside.L_meta_5218.wv at hd
      have m1 := PEqualNP.Outside.L_meta_5218.run_mono C.gates hm
        (List.ofFn (Function.update x v false)) (List.ofFn x) (by simp) (by
          intro i hi
          by_cases hin : i < n
          · rw [PEqualNP.Outside.L_meta_5218.getD_ofFn _ _ hin] at hi ⊢
            by_cases hiv : (⟨i, hin⟩ : Fin n) = v
            · rw [hiv, Function.update_self] at hi
              exact Bool.noConfusion hi
            · rw [Function.update_of_ne hiv] at hi
              exact hi
          · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
            exact Bool.noConfusion hi) (n + j)
      have m0 := PEqualNP.Outside.L_meta_5218.run_mono C.gates hm
        (List.replicate n false) (List.ofFn (Function.update x v false)) (by simp) (by
          intro i hi
          exfalso
          by_cases hin : i < n
          · rw [List.getD_eq_getElem _ _ (by simpa using hin)] at hi
            simp at hi
          · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
            exact Bool.noConfusion hi) (n + j)
      refine ⟨hjl, ?_, x, hx, ?_⟩
      · show (PEqualNP.Outside.L_meta_5218.run C.gates (List.replicate n false)).getD (n + j) false = false
        revert hd m1 m0
        cases (PEqualNP.Outside.L_meta_5218.run C.gates (List.replicate n false)).getD (n + j) false <;>
        cases (PEqualNP.Outside.L_meta_5218.run C.gates (List.ofFn x)).getD (n + j) false <;>
        cases (PEqualNP.Outside.L_meta_5218.run C.gates (List.ofFn (Function.update x v false))).getD (n + j) false <;>
        simp
      · show (PEqualNP.Outside.L_meta_5218.run C.gates (List.ofFn x)).getD (n + j) false = true
        revert hd m1
        cases (PEqualNP.Outside.L_meta_5218.run C.gates (List.ofFn x)).getD (n + j) false <;>
        cases (PEqualNP.Outside.L_meta_5218.run C.gates (List.ofFn (Function.update x v false))).getD (n + j) false <;>
        simp
    rw [← Fintype.card_coe D]
    apply Fintype.card_le_of_injective
      (fun j : D => ⟨⟨j.1, (hP j.1 j.2).1⟩, (hP j.1 j.2).2⟩)
    intro a b hab
    apply Subtype.ext
    have := congrArg (fun z => (z.1 : ℕ)) hab
    exact this
  omega
