import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8287

open Classical

noncomputable def Q {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => G.Adj p.1 p.2 ∧ p.1 ∈ S)

noncomputable def d {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun v => G.Adj u v)).card

theorem d_eq {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) : d G u = (G.neighborSet u).ncard := by
  unfold d
  rw [← Set.ncard_coe_finset]
  congr 1
  ext v
  simp

theorem mem_Q {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (a b : Fin n) :
    (a, b) ∈ Q G S ↔ G.Adj a b ∧ a ∈ S := by
  unfold Q
  rw [Finset.mem_filter]
  simp

theorem Q_card {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    (Q G S).card = ∑ u ∈ S, d G u := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := S)]
  · apply Finset.sum_congr rfl
    intro u hu
    unfold d
    refine Eq.trans (congrArg Finset.card ?_) (Finset.card_image_of_injective _ (Prod.mk_right_injective u))
    ext ⟨a, b⟩
    rw [Finset.mem_filter, mem_Q, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h⟩
      subst h
      exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩, rfl⟩
    · rintro ⟨v, hv, h⟩
      rw [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨(Finset.mem_filter.mp hv).2, hu⟩, rfl⟩
  · rintro ⟨a, b⟩ hp
    exact ((mem_Q G S a b).mp hp).2

end PEqualNP.Outside.L_meta_8287

theorem PEqualNP.Outside.L_meta_8287 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)), x2.Colorable (2 : ℕ) → (∀ x5 ∉ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 x7 : Fin x1), x2.Adj x6 x7 → x6 ∉ x3) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → ∀ (x8 : Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∈ x8 ∨ x10 ∈ x8) → (Finset.univ \ x3).card / (2 : ℕ) ≤ x8.card := by
  classical
  intro n G I _ h3 hI _ C hC
  have hM : (PEqualNP.Outside.L_meta_8287.Q G (Finset.univ \ I)).card = 3 * (Finset.univ \ I).card := by
    rw [PEqualNP.Outside.L_meta_8287.Q_card, Finset.sum_congr rfl (g := fun _ => 3), Finset.sum_const,
      smul_eq_mul, mul_comm]
    intro u hu
    rw [PEqualNP.Outside.L_meta_8287.d_eq]
    exact h3 u (by simpa using hu)
  have hCc : (PEqualNP.Outside.L_meta_8287.Q G C).card ≤ 3 * C.card := by
    rw [PEqualNP.Outside.L_meta_8287.Q_card, mul_comm, ← smul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro u _
    by_cases hu : u ∈ I
    · have : PEqualNP.Outside.L_meta_8287.d G u = 0 := by
        unfold PEqualNP.Outside.L_meta_8287.d
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro v _ hv
        exact hI u v hv hu
      omega
    · rw [PEqualNP.Outside.L_meta_8287.d_eq, h3 u hu]
  have hsub : PEqualNP.Outside.L_meta_8287.Q G (Finset.univ \ I) ⊆
      PEqualNP.Outside.L_meta_8287.Q G C ∪ (PEqualNP.Outside.L_meta_8287.Q G C).image Prod.swap := by
    rintro ⟨a, b⟩ hp
    rw [PEqualNP.Outside.L_meta_8287.mem_Q] at hp
    rw [Finset.mem_union]
    rcases hC a b hp.1 with h | h
    · left
      rw [PEqualNP.Outside.L_meta_8287.mem_Q]
      exact ⟨hp.1, h⟩
    · right
      rw [Finset.mem_image]
      refine ⟨(b, a), ?_, rfl⟩
      rw [PEqualNP.Outside.L_meta_8287.mem_Q]
      exact ⟨hp.1.symm, h⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (PEqualNP.Outside.L_meta_8287.Q G C)
    ((PEqualNP.Outside.L_meta_8287.Q G C).image Prod.swap)
  have h4 : ((PEqualNP.Outside.L_meta_8287.Q G C).image Prod.swap).card ≤
      (PEqualNP.Outside.L_meta_8287.Q G C).card := Finset.card_image_le
  omega
