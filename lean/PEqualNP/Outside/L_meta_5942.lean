import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5942

theorem nmono {x1 x2 : Type} (x5 : Finset x2) (x6 : x2 → x1 → Bool) {S T : Finset x1}
    (h : S ⊆ T) :
    ({b ∈ x5 | ∃ a ∈ S, x6 b a = Bool.true} : Finset x2) ⊆
      {b ∈ x5 | ∃ a ∈ T, x6 b a = Bool.true} := by
  intro b hb
  simp only [Finset.mem_filter] at hb ⊢
  obtain ⟨hb5, a, ha, hab⟩ := hb
  exact ⟨hb5, a, h ha, hab⟩

theorem aux {x1 x2 : Type} [DecidableEq x1] (x5 : Finset x2) (x6 : x2 → x1 → Bool) (q : ℕ) :
    ∀ n : ℕ, ∀ X : Finset x1, X.card = n →
      q * ({b ∈ x5 | ∃ a ∈ X, x6 b a = Bool.true} : Finset x2).card < X.card →
      ∃ Y ⊆ X, q * ({b ∈ x5 | ∃ a ∈ Y, x6 b a = Bool.true} : Finset x2).card < Y.card ∧
        ∀ Y' ⊆ Y, Y'.card < Y.card →
          Y'.card ≤ q * ({b ∈ x5 | ∃ a ∈ Y', x6 b a = Bool.true} : Finset x2).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X hn hX
    by_cases hmin : ∀ Y' ⊆ X, Y'.card < X.card →
          Y'.card ≤ q * ({b ∈ x5 | ∃ a ∈ Y', x6 b a = Bool.true} : Finset x2).card
    · exact ⟨X, Finset.Subset.refl X, hX, hmin⟩
    · push Not at hmin
      obtain ⟨Y', hY'X, hlt, hbad⟩ := hmin
      obtain ⟨Y, hYY', h1, h2⟩ := ih Y'.card (hn ▸ hlt) Y' rfl hbad
      exact ⟨Y, hYY'.trans hY'X, h1, h2⟩

end PEqualNP.Outside.L_meta_5942

theorem PEqualNP.Outside.L_meta_5942 : ∀ (x1 x2 : Type) [x3 : DecidableEq x1] [x4 : DecidableEq x2] (x5 : Finset x2) (x6 : x2 → x1 → Bool) (x7 : ℕ) (x8 : Finset x1),   have x9 : Finset x1 → Finset x2 := fun (x9 : Finset x1) => {x10 ∈ x5 | ∃ x11 ∈ x9, x6 x10 x11 = Bool.true};   x7 * (x9 x8).card < x8.card → ∃ x11 ⊆ x8, x11.card = x7 * (x9 x11).card + (1 : ℕ) ∧ ∀ x12 ⊆ x9 x11, x12.Nonempty → x7 * x12.card < {x15 ∈ x11 | ∃ x16 ∈ x12, x6 x16 x15 = Bool.true}.card := by
  intro x1 x2 x3 x4 x5 x6 q X
  dsimp only
  intro hX
  obtain ⟨Y, hYX, hlt, hmin⟩ := PEqualNP.Outside.L_meta_5942.aux x5 x6 q X.card X rfl hX
  have hcard : Y.card = q * ({b ∈ x5 | ∃ a ∈ Y, x6 b a = Bool.true} : Finset x2).card + 1 := by
    have hpos : 0 < Y.card := by omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
    have h1 := hmin (Y.erase y) (Finset.erase_subset y Y) (Finset.card_erase_lt_of_mem hy)
    rw [Finset.card_erase_of_mem hy] at h1
    have h2 := Nat.mul_le_mul_left q (Finset.card_le_card
      (PEqualNP.Outside.L_meta_5942.nmono x5 x6 (Finset.erase_subset y Y)))
    omega
  refine ⟨Y, hYX, hcard, ?_⟩
  intro B hB hne
  have hZY : ({a ∈ Y | ∃ b ∈ B, x6 b a = Bool.true} : Finset x1) ⊆ Y := Finset.filter_subset _ _
  have hZpos : 0 < ({a ∈ Y | ∃ b ∈ B, x6 b a = Bool.true} : Finset x1).card := by
    obtain ⟨b, hb⟩ := hne
    have hbN := hB hb
    simp only [Finset.mem_filter] at hbN
    obtain ⟨_, a, ha, hab⟩ := hbN
    exact Finset.card_pos.mpr ⟨a, by
      simp only [Finset.mem_filter]
      exact ⟨ha, b, hb, hab⟩⟩
  have hs1 := Finset.card_sdiff_add_card_eq_card hZY
  have hs2 := Finset.card_sdiff_add_card_eq_card hB
  have h1 := hmin (Y \ {a ∈ Y | ∃ b ∈ B, x6 b a = Bool.true}) Finset.sdiff_subset (by omega)
  have hsub : ({b ∈ x5 | ∃ a ∈ Y \ {a ∈ Y | ∃ b ∈ B, x6 b a = Bool.true}, x6 b a = Bool.true} : Finset x2)
      ⊆ ({b ∈ x5 | ∃ a ∈ Y, x6 b a = Bool.true} : Finset x2) \ B := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_sdiff] at hb ⊢
    obtain ⟨hb5, a, ⟨haY, hna⟩, hab⟩ := hb
    exact ⟨⟨hb5, a, haY, hab⟩, fun hbB => hna ⟨haY, b, hbB, hab⟩⟩
  have h2 := Nat.mul_le_mul_left q (Finset.card_le_card hsub)
  have h3 : q * ({b ∈ x5 | ∃ a ∈ Y, x6 b a = Bool.true} : Finset x2).card
      = q * (({b ∈ x5 | ∃ a ∈ Y, x6 b a = Bool.true} : Finset x2) \ B).card + q * B.card := by
    rw [← Nat.mul_add, hs2]
  omega
