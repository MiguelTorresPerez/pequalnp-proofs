import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5337

lemma core (n k : ℕ) (E : Finset (Fin n × Fin n)) : ∀ s : ℕ, ∀ A B : Finset (Fin n),
    A.card + B.card = s →
    k * (A.card + B.card) < (E.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).card →
    ∃ (A' : Finset (Fin n)) (B' : Finset (Fin n)), A'.Nonempty ∧ B'.Nonempty ∧
      (∀ a ∈ A', k < (B'.filter (fun b => (a, b) ∈ E)).card) ∧
      ∀ b ∈ B', k < (A'.filter (fun a => (a, b) ∈ E)).card := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro A B hs hgood
    by_cases hA : ∀ a ∈ A, k < (B.filter (fun b => (a, b) ∈ E)).card
    · by_cases hB : ∀ b ∈ B, k < (A.filter (fun a => (a, b) ∈ E)).card
      · have hpos : 0 < (E.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).card := by omega
        obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
        rw [Finset.mem_filter] at hp
        exact ⟨A, B, ⟨p.1, hp.2.1⟩, ⟨p.2, hp.2.2⟩, hA, hB⟩
      · push Not at hB
        obtain ⟨b, hb, hdeg⟩ := hB
        have hc := Finset.card_erase_add_one hb
        have hsub : E.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B) ⊆
            E.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B.erase b) ∪
              (A.filter (fun a => (a, b) ∈ E)).image (fun a => (a, b)) := by
          intro p hp
          rw [Finset.mem_filter] at hp
          rw [Finset.mem_union]
          by_cases hpb : p.2 = b
          · right
            rw [Finset.mem_image]
            refine ⟨p.1, ?_, ?_⟩
            · rw [Finset.mem_filter]
              refine ⟨hp.2.1, ?_⟩
              rw [← hpb]
              exact hp.1
            · rw [← hpb]
          · left
            rw [Finset.mem_filter]
            exact ⟨hp.1, hp.2.1, Finset.mem_erase.mpr ⟨hpb, hp.2.2⟩⟩
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_union_le (E.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B.erase b))
          ((A.filter (fun a => (a, b) ∈ E)).image (fun a => (a, b)))
        have h3 : ((A.filter (fun a => (a, b) ∈ E)).image (fun a => (a, b))).card ≤
            (A.filter (fun a => (a, b) ∈ E)).card := Finset.card_image_le
        have h4 : k * (A.card + B.card) = k * (A.card + (B.erase b).card) + k := by
          rw [← hc]; ring
        exact ih (A.card + (B.erase b).card) (by omega) A (B.erase b) rfl (by omega)
    · push Not at hA
      obtain ⟨a, ha, hdeg⟩ := hA
      have hc := Finset.card_erase_add_one ha
      have hsub : E.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B) ⊆
          E.filter (fun p => p.1 ∈ A.erase a ∧ p.2 ∈ B) ∪
            (B.filter (fun b => (a, b) ∈ E)).image (fun b => (a, b)) := by
        intro p hp
        rw [Finset.mem_filter] at hp
        rw [Finset.mem_union]
        by_cases hpa : p.1 = a
        · right
          rw [Finset.mem_image]
          refine ⟨p.2, ?_, ?_⟩
          · rw [Finset.mem_filter]
            refine ⟨hp.2.2, ?_⟩
            rw [← hpa]
            exact hp.1
          · rw [← hpa]
        · left
          rw [Finset.mem_filter]
          exact ⟨hp.1, Finset.mem_erase.mpr ⟨hpa, hp.2.1⟩, hp.2.2⟩
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (E.filter (fun p => p.1 ∈ A.erase a ∧ p.2 ∈ B))
        ((B.filter (fun b => (a, b) ∈ E)).image (fun b => (a, b)))
      have h3 : ((B.filter (fun b => (a, b) ∈ E)).image (fun b => (a, b))).card ≤
          (B.filter (fun b => (a, b) ∈ E)).card := Finset.card_image_le
      have h4 : k * (A.card + B.card) = k * ((A.erase a).card + B.card) + k := by
        rw [← hc]; ring
      exact ih ((A.erase a).card + B.card) (by omega) (A.erase a) B rfl (by omega)

end PEqualNP.Outside.L_meta_5337

theorem PEqualNP.Outside.L_meta_5337 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x1)), x2 * (x1 + x1) < x3.card → ∃ (x5 : Finset (Fin x1)) (x6 : Finset (Fin x1)), x5.Nonempty ∧ x6.Nonempty ∧ (∀ x7 ∈ x5, x2 < {x9 ∈ x6 | (x7, x9) ∈ x3}.card) ∧ ∀ x7 ∈ x6, x2 < {x9 ∈ x5 | (x9, x7) ∈ x3}.card := by
  intro n k E h
  refine PEqualNP.Outside.L_meta_5337.core n k E _ Finset.univ Finset.univ rfl ?_
  simpa using h
