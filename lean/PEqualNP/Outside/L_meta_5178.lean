import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5178

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.ReadK PEqualNP.MetaComplexity

def pts {n : ℕ} (S : Finset (Fin (n + n))) : Finset (Fin n) :=
  Finset.univ.filter fun p => Fin.castAdd n p ∈ S

def lns {n : ℕ} (S : Finset (Fin (n + n))) : Finset (Fin n) :=
  ((List.finRange n).filter fun l => decide (Fin.natAdd n l ∈ S)).toFinset

lemma mem_pts {n : ℕ} (S : Finset (Fin (n + n))) (p : Fin n) :
    p ∈ pts S ↔ Fin.castAdd n p ∈ S := by
  simp [pts]

lemma mem_lns {n : ℕ} (S : Finset (Fin (n + n))) (l : Fin n) :
    l ∈ lns S ↔ Fin.natAdd n l ∈ S := by
  simp [lns]

lemma card_lns {n : ℕ} (S : Finset (Fin (n + n))) :
    (lns S).card = List.countP (fun l : Fin n => decide (Fin.natAdd n l ∈ S)) (List.finRange n) := by
  unfold lns
  rw [List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _), List.countP_eq_length_filter]

lemma fun_eq {n : ℕ} (C : Circuit) (S : Finset (Fin (n + n))) (X Y : Finset (Fin n))
    (hX : ∀ p, p ∈ X ↔ Fin.castAdd n p ∈ S) (hY : ∀ l, l ∈ Y ↔ Fin.natAdd n l ∈ S) :
    circuitFun (n + n) C (setInput S) = C.eval (incidenceInput X Y) := by
  unfold circuitFun incidenceInput
  rw [List.ofFn_add]
  congr 2
  · congr 1
    funext p
    simp only [setInput, hX]
    rfl
  · congr 1
    funext l
    simp only [setInput, hY]

lemma cast_ne_nat {n : ℕ} (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

lemma pairX {n : ℕ} (p l q : Fin n) : q ∈ ({p} : Finset (Fin n)) ↔
    Fin.castAdd n q ∈ ({Fin.castAdd n p, Fin.natAdd n l} : Finset (Fin (n + n))) := by
  rw [Finset.mem_singleton, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    left
    rw [h]
  · rintro (h | h)
    · exact Fin.castAdd_injective n n h
    · exact absurd h (cast_ne_nat _ _)

lemma pairY {n : ℕ} (p l q : Fin n) : q ∈ ({l} : Finset (Fin n)) ↔
    Fin.natAdd n q ∈ ({Fin.castAdd n p, Fin.natAdd n l} : Finset (Fin (n + n))) := by
  rw [Finset.mem_singleton, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    right
    rw [h]
  · rintro (h | h)
    · exact absurd h.symm (cast_ne_nat _ _)
    · exact Fin.natAdd_injective n n h

end PEqualNP.Outside.L_meta_5178

theorem PEqualNP.Outside.L_meta_5178 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (1 : ℕ) ≤ x1 → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x7 x8 : Finset (Fin x2)), x8.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x7 x8 → x4.eval (PEqualNP.GenericRejection.incidenceInput x7 x8) = Bool.false) → ∀ (x8 : Finset (Fin (x2 + x2))), List.countP (fun (x9 : Fin x2) => Decidable.decide (Fin.natAdd x2 x9 ∈ x8)) (List.finRange x2) ≤ x1 → (PEqualNP.ReadK.IsPrimeImplicant (x2 + x2) x4 x8 ↔ ∃ (x10 : Fin x2) (x11 : Fin x2), x10 ∈ x3 x11 ∧ x8 = {Fin.castAdd x2 x10, Fin.natAdd x2 x11}) := by
  intro k n S C hk hR hF T hT
  have key := PEqualNP.Outside.L_meta_5178.fun_eq (n := n) C
  constructor
  · rintro ⟨h1, h2⟩
    rw [key T _ _ (PEqualNP.Outside.L_meta_5178.mem_pts T)
      (PEqualNP.Outside.L_meta_5178.mem_lns T)] at h1
    have hnf : ¬ PEqualNP.GenericRejection.IsFalseInput S
        (PEqualNP.Outside.L_meta_5178.pts T) (PEqualNP.Outside.L_meta_5178.lns T) := by
      intro hf
      have := hF _ _ (by rw [PEqualNP.Outside.L_meta_5178.card_lns]; exact hT) hf
      rw [this] at h1
      exact Bool.noConfusion h1
    unfold PEqualNP.GenericRejection.IsFalseInput at hnf
    push Not at hnf
    obtain ⟨l, hl, hd⟩ := hnf
    rw [Finset.not_disjoint_iff] at hd
    obtain ⟨p, hp, hpX⟩ := hd
    rw [PEqualNP.Outside.L_meta_5178.mem_pts] at hpX
    rw [PEqualNP.Outside.L_meta_5178.mem_lns] at hl
    refine ⟨p, l, hp, ?_⟩
    by_contra hne
    have hsub : ({Fin.castAdd n p, Fin.natAdd n l} : Finset (Fin (n + n))) ⊆ T := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hpX
      · exact hl
    have hss : ({Fin.castAdd n p, Fin.natAdd n l} : Finset (Fin (n + n))) ∈ T.ssubsets := by
      rw [Finset.mem_ssubsets]
      exact lt_of_le_of_ne hsub (fun h => hne h.symm)
    have h3 := h2 _ hss
    rw [key _ {p} {l} (PEqualNP.Outside.L_meta_5178.pairX p l) (PEqualNP.Outside.L_meta_5178.pairY p l), hR l p hp] at h3
    exact Bool.noConfusion h3
  · rintro ⟨p, l, hp, rfl⟩
    constructor
    · rw [key _ {p} {l} (PEqualNP.Outside.L_meta_5178.pairX p l) (PEqualNP.Outside.L_meta_5178.pairY p l)]
      exact hR l p hp
    · intro U hU
      rw [Finset.mem_ssubsets] at hU
      rw [key U _ _ (PEqualNP.Outside.L_meta_5178.mem_pts U)
        (PEqualNP.Outside.L_meta_5178.mem_lns U)]
      have hYsub : PEqualNP.Outside.L_meta_5178.lns U ⊆ {l} := by
        intro l' hl'
        rw [PEqualNP.Outside.L_meta_5178.mem_lns] at hl'
        have := hU.1 hl'
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h
        · exact absurd h.symm (PEqualNP.Outside.L_meta_5178.cast_ne_nat _ _)
        · simpa using Fin.natAdd_injective n n h
      have hXsub : PEqualNP.Outside.L_meta_5178.pts U ⊆ {p} := by
        intro q hq
        rw [PEqualNP.Outside.L_meta_5178.mem_pts] at hq
        have := hU.1 hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h
        · simpa using Fin.castAdd_injective n n h
        · exact absurd h (PEqualNP.Outside.L_meta_5178.cast_ne_nat _ _)
      apply hF
      · calc (PEqualNP.Outside.L_meta_5178.lns U).card ≤ ({l} : Finset (Fin n)).card :=
              Finset.card_le_card hYsub
          _ = 1 := Finset.card_singleton l
          _ ≤ k := hk
      · intro l' hl'
        rw [Finset.disjoint_left]
        intro q _ hq
        have e1 : l' = l := by simpa using hYsub hl'
        have e2 : q = p := by simpa using hXsub hq
        subst e1 e2
        rw [PEqualNP.Outside.L_meta_5178.mem_lns] at hl'
        rw [PEqualNP.Outside.L_meta_5178.mem_pts] at hq
        apply hU.2
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact hq
        · exact hl'
