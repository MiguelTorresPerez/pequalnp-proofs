import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_1046
theorem inv {α : Type*} [DecidableEq α] (F : Finset α → ℤ) (Y : Finset α) :
    ∑ S ∈ Y.powerset, ∑ T ∈ S.powerset, (-1 : ℤ) ^ (S.card - T.card) * F T = F Y := by
  rw [Finset.sum_comm' (t' := Y.powerset) (s' := fun T => Y.powerset.filter (fun S => T ⊆ S))]
  · rw [Finset.sum_eq_single_of_mem Y (Finset.mem_powerset_self Y)]
    · have hY : Y.powerset.filter (fun S => Y ⊆ S) = {Y} := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, h2⟩
          exact Finset.Subset.antisymm h1 h2
        · rintro rfl
          exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
      rw [hY, Finset.sum_singleton, Nat.sub_self, pow_zero, one_mul]
    · intro T hT hTY
      have hTY' : T ⊆ Y := Finset.mem_powerset.mp hT
      rw [← Finset.sum_mul]
      apply mul_eq_zero_of_left
      have e : ∑ S ∈ Y.powerset.filter (fun S => T ⊆ S), (-1 : ℤ) ^ (S.card - T.card)
          = ∑ U ∈ (Y \ T).powerset, (-1 : ℤ) ^ U.card := by
        apply Finset.sum_nbij' (fun S => S \ T) (fun U => U ∪ T)
        · intro S hS
          simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
          exact Finset.sdiff_subset_sdiff hS.1 (Finset.Subset.refl T)
        · intro U hU
          simp only [Finset.mem_filter, Finset.mem_powerset] at hU ⊢
          exact ⟨Finset.union_subset (hU.trans Finset.sdiff_subset) hTY',
            Finset.subset_union_right⟩
        · intro S hS
          simp only [Finset.mem_filter, Finset.mem_powerset] at hS
          exact Finset.sdiff_union_of_subset hS.2
        · intro U hU
          simp only [Finset.mem_powerset] at hU
          apply Finset.union_sdiff_cancel_right
          exact Finset.disjoint_of_subset_left hU Finset.sdiff_disjoint
        · intro S hS
          simp only [Finset.mem_filter, Finset.mem_powerset] at hS
          rw [Finset.card_sdiff_of_subset hS.2]
      rw [e, Finset.sum_powerset_neg_one_pow_card]
      have hne : Y \ T ≠ ∅ := by
        intro h
        rw [Finset.sdiff_eq_empty_iff_subset] at h
        exact hTY (Finset.Subset.antisymm hTY' h)
      rw [if_neg hne]
  · intro S T
    simp only [Finset.mem_powerset, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2⟩, h2.trans h1⟩
    · rintro ⟨⟨h1, h2⟩, _⟩
      exact ⟨h1, h2⟩
theorem apex_le {n t : ℕ} (par : Fin (t+1) → Fin (t+1)) (B : Fin (t+1) → Finset (Fin n))
    (hpar : ∀ i, i ≠ 0 → par i < i) (v : Fin n) (a : Fin (t+1))
    (ha : ∀ i, v ∈ B i → i ≠ a → i ≠ 0 ∧ v ∈ B (par i)) :
    ∀ j, v ∈ B j → a ≤ j := by
  have key : ∀ k : ℕ, ∀ j : Fin (t+1), j.val = k → v ∈ B j → a ≤ j := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro j hk hv
      by_cases hja : j = a
      · exact le_of_eq hja.symm
      · obtain ⟨h0, hp⟩ := ha j hv hja
        have hlt : par j < j := hpar j h0
        have hlt' : (par j).val < k := by
          rw [← hk]
          exact hlt
        exact le_of_lt (lt_of_le_of_lt (ih _ hlt' (par j) rfl hp) hlt)
  exact fun j hv => key j.val j rfl hv
theorem count_cov {n t : ℕ} (par : Fin (t+1) → Fin (t+1)) (B : Fin (t+1) → Finset (Fin n))
    (hpar : ∀ i, i ≠ 0 → par i < i)
    (hrun : ∀ v : Fin n, (∃ i, v ∈ B i) → ∃ a, v ∈ B a ∧
      ∀ i, v ∈ B i → i ≠ a → i ≠ 0 ∧ v ∈ B (par i))
    (S : Finset (Fin n)) (h : ∃ i, S ⊆ B i) (x : ℤ) :
    (∑ i, if S ⊆ B i then x else 0) -
      (∑ i ∈ Finset.univ.erase 0, if S ⊆ B i ∧ S ⊆ B (par i) then x else 0) = x := by
  have hne : (Finset.univ.filter (fun i => S ⊆ B i)).Nonempty := by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨m, hmS, hmin⟩ : ∃ m : Fin (t+1), S ⊆ B m ∧ ∀ i, S ⊆ B i → m ≤ i := by
    refine ⟨(Finset.univ.filter (fun i => S ⊆ B i)).min' hne, ?_, ?_⟩
    · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
    · intro i hi
      apply Finset.min'_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  have htop : ∀ i, S ⊆ B i → (i = 0 ∨ ¬ S ⊆ B (par i)) → i = m := by
    intro i hi hti
    refine le_antisymm ?_ (hmin i hi)
    rcases hti with h0 | hp
    · rw [h0]
      exact Fin.zero_le _
    · obtain ⟨v, hvS, hvp⟩ := Finset.not_subset.mp hp
      obtain ⟨a, _, ha⟩ := hrun v ⟨i, hi hvS⟩
      have hia : i = a := by
        by_contra hne'
        exact hvp (ha i (hi hvS) hne').2
      rw [hia]
      exact apex_le par B hpar v a ha m (hmS hvS)
  have hpt : ∀ i, (if S ⊆ B i then x else 0) = (if i = m then x else 0) +
      (if i ≠ 0 then (if S ⊆ B i ∧ S ⊆ B (par i) then x else 0) else 0) := by
    intro i
    by_cases hi : S ⊆ B i
    · by_cases him : i = m
      · have hz : (if i ≠ 0 then (if S ⊆ B i ∧ S ⊆ B (par i) then x else 0) else 0) = 0 := by
          by_cases h0 : i = 0
          · rw [if_neg (not_not.mpr h0)]
          · have hq : ¬ (S ⊆ B i ∧ S ⊆ B (par i)) := by
              rintro ⟨-, hp⟩
              have h1 := hmin (par i) hp
              have h2 := hpar i h0
              rw [← him] at h1
              exact absurd h2 (not_lt.mpr h1)
            rw [if_pos h0, if_neg hq]
        rw [hz, if_pos hi, if_pos him, add_zero]
      · have hc : i ≠ 0 ∧ S ⊆ B (par i) := by
          by_contra hc
          apply him
          apply htop i hi
          by_cases h0 : i = 0
          · exact Or.inl h0
          · right
            intro hp
            exact hc ⟨h0, hp⟩
        rw [if_pos hi, if_neg him, if_pos hc.1, if_pos ⟨hi, hc.2⟩, zero_add]
    · have him : i ≠ m := fun e => hi (e ▸ hmS)
      simp [hi, him]
  have hsum : (∑ i, if S ⊆ B i then x else 0) = ∑ i, ((if i = m then x else 0) +
      (if i ≠ 0 then (if S ⊆ B i ∧ S ⊆ B (par i) then x else 0) else 0)) :=
    Finset.sum_congr rfl (fun i _ => hpt i)
  rw [hsum, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ m),
    ← Finset.sum_filter, Finset.filter_ne', add_sub_cancel_right]
theorem approx_eq {n t : ℕ} (F : Finset (Fin n) → ℤ) (par : Fin (t+1) → Fin (t+1))
    (B : Fin (t+1) → Finset (Fin n))
    (hpar : ∀ i, i ≠ 0 → par i < i)
    (hrun : ∀ v : Fin n, (∃ i, v ∈ B i) → ∃ a, v ∈ B a ∧
      ∀ i, v ∈ B i → i ≠ a → i ≠ 0 ∧ v ∈ B (par i))
    {inst : DecidablePred (fun S : Finset (Fin n) => ∃ i, S ⊆ B i)} (X : Finset (Fin n)) :
    (∑ i, F (X ∩ B i)) - ∑ i ∈ Finset.univ.erase (0 : Fin (t+1)), F (X ∩ B i ∩ B (par i))
      = (X.powerset.filter (fun S => ∃ i, S ⊆ B i)).sum
          (fun S => S.powerset.sum (fun T => (-1 : Int)^(S.card-T.card)*F T)) := by
  have hinv : ∀ Y, F Y = ∑ S ∈ Y.powerset,
      S.powerset.sum (fun T => (-1 : Int)^(S.card-T.card)*F T) :=
    fun Y => (inv F Y).symm
  have h1 : ∀ i, F (X ∩ B i) = ∑ S ∈ X.powerset,
      if S ⊆ B i then S.powerset.sum (fun T => (-1 : Int)^(S.card-T.card)*F T) else 0 := by
    intro i
    rw [hinv, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext S
    simp only [Finset.mem_powerset, Finset.mem_filter, Finset.subset_inter_iff]
  have h2 : ∀ i, F (X ∩ B i ∩ B (par i)) = ∑ S ∈ X.powerset,
      if S ⊆ B i ∧ S ⊆ B (par i) then
        S.powerset.sum (fun T => (-1 : Int)^(S.card-T.card)*F T) else 0 := by
    intro i
    rw [hinv, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext S
    simp only [Finset.mem_powerset, Finset.mem_filter, Finset.subset_inter_iff, and_assoc]
  simp only [h1, h2]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ.erase 0), ← Finset.sum_sub_distrib,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs with hS
  · exact count_cov par B hpar hrun S hS _
  · simp only [not_exists] at hS
    simp [hS]
theorem core {α : Type*} [DecidableEq α] (F : Finset α → ℤ) (D : Finset (Finset α))
    (coef : Finset α → ℤ) (covered : Finset α → Prop) {inst : DecidablePred covered}
    (approx : Finset α → ℤ)
    (hD : ∀ X ∈ D, ∀ Y ⊆ X, Y ∈ D)
    (hinv : ∀ Y, ∑ S ∈ Y.powerset, coef S = F Y)
    (happrox : ∀ X, approx X = (X.powerset.filter covered).sum coef) :
    (∀ X ∈ D, approx X = (X.powerset.filter covered).sum coef) ∧
    ((∀ X ∈ D, approx X = F X) ↔ ∀ S ∈ D, coef S ≠ 0 → covered S) ∧
    ∀ S ∈ D, ¬covered S → coef S ≠ 0 →
      (∀ T ⊂ S, ¬covered T → coef T = 0) →
      F S - approx S = coef S ∧ ∀ T ⊂ S, F T = approx T := by
  have herr : ∀ X, F X - approx X = ∑ S ∈ X.powerset.filter (fun S => ¬ covered S), coef S := by
    intro X
    rw [happrox, ← hinv X, ← Finset.sum_filter_add_sum_filter_not X.powerset covered]
    ring
  refine ⟨fun X _ => happrox X, ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · have key : ∀ k : ℕ, ∀ S ∈ D, S.card = k → ¬ covered S → coef S = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro S hS hk hc
        have e := herr S
        rw [h S hS, sub_self, Finset.sum_eq_single_of_mem S] at e
        · exact e.symm
        · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset_self S, hc⟩
        · intro U hU hUS
          obtain ⟨hU1, hU2⟩ := Finset.mem_filter.mp hU
          have hsub : U ⊆ S := Finset.mem_powerset.mp hU1
          have hlt : U.card < k := by
            rw [← hk]
            exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hUS⟩)
          exact ih U.card hlt U (hD S hS U hsub) rfl hU2
    intro S hS hne
    by_contra hc
    exact hne (key S.card S hS rfl hc)
  · intro X hX
    have e := herr X
    have hz : ∑ S ∈ X.powerset.filter (fun S => ¬ covered S), coef S = 0 := by
      apply Finset.sum_eq_zero
      intro U hU
      obtain ⟨hU1, hU2⟩ := Finset.mem_filter.mp hU
      by_contra hc
      exact hU2 (h U (hD X hX U (Finset.mem_powerset.mp hU1)) hc)
    rw [hz] at e
    linarith
  · intro S _ hnc _ hmin
    refine ⟨?_, ?_⟩
    · rw [herr S]
      apply Finset.sum_eq_single_of_mem S
      · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset_self S, hnc⟩
      · intro U hU hUS
        obtain ⟨hU1, hU2⟩ := Finset.mem_filter.mp hU
        exact hmin U (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hU1, hUS⟩) hU2
    · intro T hT
      have e := herr T
      have hz : ∑ U ∈ T.powerset.filter (fun S => ¬ covered S), coef U = 0 := by
        apply Finset.sum_eq_zero
        intro U hU
        obtain ⟨hU1, hU2⟩ := Finset.mem_filter.mp hU
        exact hmin U (Finset.ssubset_of_subset_of_ssubset (Finset.mem_powerset.mp hU1) hT) hU2
      rw [hz] at e
      linarith
end PEqualNP.Outside.L_lib_1046
theorem PEqualNP.Outside.L_lib_1046 : ∀ (n t : Nat) (F : Finset (Fin n) → Int) (D : Finset (Finset (Fin n)))
    (par : Fin (t+1) → Fin (t+1)) (B : Fin (t+1) → Finset (Fin n)),
  (∀ X ∈ D, ∀ Y ⊆ X, Y ∈ D) → par 0 = 0 → (∀ i, i ≠ 0 → par i < i) →
  (∀ v : Fin n, (∃ i, v ∈ B i) → ∃ a, v ∈ B a ∧
    ∀ i, v ∈ B i → i ≠ a → i ≠ 0 ∧ v ∈ B (par i)) →
  let coef := fun S : Finset (Fin n) =>
    S.powerset.sum (fun T => (-1 : Int)^(S.card-T.card)*F T)
  let covered := fun S : Finset (Fin n) => ∃ i, S ⊆ B i
  let approx := fun X : Finset (Fin n) =>
    (∑ i, F (X ∩ B i)) - ∑ i ∈ Finset.univ.erase (0 : Fin (t+1)), F (X ∩ B i ∩ B (par i))
  (∀ X ∈ D, approx X = (X.powerset.filter covered).sum coef) ∧
  ((∀ X ∈ D, approx X = F X) ↔ ∀ S ∈ D, coef S ≠ 0 → covered S) ∧
  ∀ S ∈ D, ¬covered S → coef S ≠ 0 →
    (∀ T ⊂ S, ¬covered T → coef T = 0) →
    F S - approx S = coef S ∧ ∀ T ⊂ S, F T = approx T := by
  intro n t F D par B hD _ hpar hrun coef covered approx
  exact PEqualNP.Outside.L_lib_1046.core F D coef covered approx hD
    (fun Y => PEqualNP.Outside.L_lib_1046.inv F Y)
    (fun X => PEqualNP.Outside.L_lib_1046.approx_eq F par B hpar hrun X)
