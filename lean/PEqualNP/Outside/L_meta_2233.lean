import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2233

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CleanedNonEdge

def orun (n : ℕ) (gs : List Gate) : List (List ℕ) := gs.foldl (orStep n) []

lemma orun_append (n : ℕ) (gs : List Gate) (a : Gate) :
    orun n (gs ++ [a]) = orStep n (orun n gs) a := by
  simp [orun, List.foldl_append]

lemma orun_length (n : ℕ) (gs : List Gate) : (orun n gs).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [orun]
  | append_singleton gs a ih => rw [orun_append]; simp [orStep, ih]

lemma pre (n : ℕ) (gs : List Gate) (a : Gate) (i : ℕ) (h : i < gs.length) :
    (orun n (gs ++ [a])).getD i [] = (orun n gs).getD i [] := by
  rw [orun_append]
  unfold orStep
  exact List.getD_append _ _ _ _ (by rw [orun_length]; exact h)

lemma getD_top {α : Type} (l : List α) (x d : α) : (l ++ [x]).getD l.length d = x := by
  simp

lemma step_mem (n : ℕ) (cs : List (List ℕ)) (a : Gate) (g : ℕ) :
    g ∈ (orStep n cs a).getD cs.length [] ↔ g = cs.length ∨ (a.op = GateOp.or ∧
      ∃ w ∈ a.inputs, n ≤ w ∧ w < n + cs.length ∧ g ∈ cs.getD (w - n) []) := by
  unfold orStep
  rw [getD_top, List.mem_cons]
  split_ifs with hop
  · rw [List.mem_flatMap]
    constructor
    · rintro (h | ⟨w, hw, hg⟩)
      · exact Or.inl h
      · rw [List.mem_filter, decide_eq_true_eq] at hw
        exact Or.inr ⟨hop, w, hw.1, hw.2.1, hw.2.2, hg⟩
    · rintro (h | ⟨_, w, hw, h1, h2, hg⟩)
      · exact Or.inl h
      · refine Or.inr ⟨w, ?_, hg⟩
        rw [List.mem_filter, decide_eq_true_eq]
        exact ⟨hw, h1, h2⟩
  · constructor
    · rintro (h | h)
      · exact Or.inl h
      · simp at h
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact absurd h hop

lemma top_mem (n : ℕ) (gs : List Gate) (a : Gate) (g : ℕ) :
    g ∈ (orun n (gs ++ [a])).getD gs.length [] ↔ g = gs.length ∨ (a.op = GateOp.or ∧
      ∃ w ∈ a.inputs, n ≤ w ∧ w < n + gs.length ∧ g ∈ (orun n gs).getD (w - n) []) := by
  rw [orun_append]
  have := step_mem n (orun n gs) a g
  rw [orun_length] at this
  exact this

lemma sets_iff (n : ℕ) (d : Gate) (gs : List Gate) : ∀ k g : ℕ,
    g ∈ (orun n gs).getD k [] ↔ k < gs.length ∧ (g = k ∨ ((gs.getD k d).op = GateOp.or ∧
      ∃ w ∈ (gs.getD k d).inputs, n ≤ w ∧ w < n + k ∧ g ∈ (orun n gs).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro k g; simp [orun]
  | append_singleton gs a ih =>
    intro k g
    rcases Nat.lt_trichotomy k gs.length with hlt | heq | hgt
    · have e : (gs ++ [a]).getD k d = gs.getD k d := List.getD_append _ _ _ _ hlt
      rw [pre n gs a k hlt, ih k g, e]
      constructor
      · rintro ⟨_, h | ⟨hop, w, hw, h1, h2, hg⟩⟩
        · exact ⟨by simp; omega, Or.inl h⟩
        · exact ⟨by simp; omega, Or.inr ⟨hop, w, hw, h1, h2, by
            rw [pre n gs a _ (by omega)]; exact hg⟩⟩
      · rintro ⟨_, h | ⟨hop, w, hw, h1, h2, hg⟩⟩
        · exact ⟨hlt, Or.inl h⟩
        · exact ⟨hlt, Or.inr ⟨hop, w, hw, h1, h2, by
            rw [pre n gs a _ (by omega)] at hg; exact hg⟩⟩
    · subst heq
      have e : (gs ++ [a]).getD gs.length d = a := by simp
      rw [top_mem, e]
      constructor
      · rintro (h | ⟨hop, w, hw, h1, h2, hg⟩)
        · exact ⟨by simp, Or.inl h⟩
        · exact ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, by
            rw [pre n gs a _ (by omega)]; exact hg⟩⟩
      · rintro ⟨_, h | ⟨hop, w, hw, h1, h2, hg⟩⟩
        · exact Or.inl h
        · exact Or.inr ⟨hop, w, hw, h1, h2, by
            rw [pre n gs a _ (by omega)] at hg; exact hg⟩
    · constructor
      · intro h
        rw [List.getD_eq_default _ _ (by rw [orun_length]; simp; omega)] at h
        simp at h
      · rintro ⟨h, _⟩
        simp at h
        omega

lemma parent (n : ℕ) (d : Gate) (gs : List Gate) : ∀ k g : ℕ, g ∈ (orun n gs).getD k [] →
    g = k ∨ ∃ h ∈ (orun n gs).getD k [], h < gs.length ∧ (gs.getD h d).op = GateOp.or ∧
      n + g ∈ (gs.getD h d).inputs := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro g hg
    obtain ⟨klt, h | ⟨hop, w, hw, h1, h2, hgw⟩⟩ := (sets_iff n d gs k g).mp hg
    · exact Or.inl h
    · right
      rcases ih (w - n) (by omega) g hgw with h | ⟨h, hh, hlt, hoph, hin⟩
      · refine ⟨k, (sets_iff n d gs k k).mpr ⟨klt, Or.inl rfl⟩, klt, hop, ?_⟩
        have : n + g = w := by omega
        rw [this]
        exact hw
      · exact ⟨h, (sets_iff n d gs k h).mpr ⟨klt, Or.inr ⟨hop, w, hw, h1, h2, hh⟩⟩,
          hlt, hoph, hin⟩

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

end PEqualNP.Outside.L_meta_2233

theorem PEqualNP.Outside.L_meta_2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C F hAO hF
  classical
  let d : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
  have hreach : ∀ g, PEqualNP.CleanedNonEdge.OrReaches n C C.output g ↔
      n ≤ C.output ∧ g ∈ (PEqualNP.Outside.L_meta_2233.orun n C.gates).getD (C.output - n) [] :=
    fun g => Iff.rfl
  have hgate : ∀ j, PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates.getD j d :=
    fun j => rfl
  let DS : Finset ℕ := (Finset.range C.gates.length).filter (fun i =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      PEqualNP.CleanedNonEdge.OrReaches n C C.output i)
  have hDS : ∀ i, i ∈ DS ↔ i < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      PEqualNP.CleanedNonEdge.OrReaches n C C.output i := by
    intro i
    simp only [DS, Finset.mem_filter, Finset.mem_range]
  have hset : {i : ℕ | i < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      PEqualNP.CleanedNonEdge.OrReaches n C C.output i} = (DS : Set ℕ) := by
    ext i
    exact (hDS i).symm
  rw [hset, Set.ncard_coe_finset]
  have hdisj : Disjoint F DS := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    have h1 := (hF j hj).2.1
    have h2 := ((hDS j).mp hj').2.1
    rw [h1] at h2
    exact PEqualNP.CircuitLowerBounds.GateOp.noConfusion h2
  have hXreach : ∀ g ∈ F ∪ DS, PEqualNP.CleanedNonEdge.OrReaches n C C.output g := by
    intro g hg
    rcases Finset.mem_union.mp hg with h | h
    · exact (hF g h).2.2
    · exact ((hDS g).mp h).2.2
  have hcount := PEqualNP.Outside.L_meta_2233.count ((F ∪ DS).image (fun j => n + j))
    (DS.image (fun j => n + j)) C.output (fun h => (C.gates.getD (h - n) d).inputs)
    (by
      intro h hh
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hh
      have hil := ((hDS i).mp hi).1
      have e : n + i - n = i := by omega
      simp only [e]
      rw [List.getD_eq_getElem _ _ hil]
      exact le_of_eq (hAO.2.2 _ (List.getElem_mem hil)))
    (by
      intro x hx hne
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hn, hmem⟩ := (hreach g).mp (hXreach g hg)
      rcases PEqualNP.Outside.L_meta_2233.parent n d C.gates _ g hmem with h | ⟨h, hh, hlt, hop, hin⟩
      · exact absurd (by omega) hne
      · refine ⟨n + h, Finset.mem_image.mpr ⟨h, (hDS h).mpr ⟨hlt, ?_, (hreach h).mpr ⟨hn, hh⟩⟩, rfl⟩, ?_⟩
        · rw [hgate]
          exact hop
        · have e : n + h - n = h := by omega
          simp only [e]
          exact hin)
  rw [Finset.card_image_of_injective _ (add_right_injective n),
    Finset.card_image_of_injective _ (add_right_injective n),
    Finset.card_union_of_disjoint hdisj] at hcount
  omega
