import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8061
end PEqualNP.Outside.L_meta_8061

theorem PEqualNP.Outside.L_meta_8061 : ∀ (x1 x2 x3 : ℕ) (x4 x5 : ℕ → ℕ) (x6 x7 x8 : ℕ → Bool),   x3 < x1 →     (∀ x10 < x2, x4 x10 < x1 + x10 ∧ x5 x10 < x1 + x10) →       (∀ x11 < x1, x8 x11 = Decidable.decide (x11 = x3)) →         (∀ x12 < x2, x8 (x1 + x12) = (x8 (x4 x12) && x6 x12 || x8 (x5 x12) && x7 x12)) →           have x13 : ℕ → ℕ → Prop := fun (x13 x14 : ℕ) => ∃ x15 < x2, x14 = x1 + x15 ∧ (x13 = x4 x15 ∧ x6 x15 = Bool.true ∨ x13 = x5 x15 ∧ x7 x15 = Bool.true);           ∀ x14 < x1 + x2, x8 x14 = Bool.true ↔ Relation.ReflTransGen x13 x3 x14 := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 h3 hlt hin hg R w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  by_cases hw1 : w < x1
  · rw [hin w hw1]
    constructor
    · intro h
      have hx : w = x3 := by simpa using h
      subst hx
      exact Relation.ReflTransGen.refl
    · intro h
      rcases Relation.ReflTransGen.cases_tail h with h | ⟨a, _, k, hk, hwk, _⟩
      · simp [h]
      · omega
  · obtain ⟨k, rfl⟩ : ∃ k, w = x1 + k := ⟨w - x1, by omega⟩
    have hk : k < x2 := by omega
    have hl := hlt k hk
    rw [hg k hk]
    constructor
    · intro h
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Relation.ReflTransGen.tail ((ih _ hl.1 (by omega)).1 h1) ⟨k, hk, rfl, Or.inl ⟨rfl, h2⟩⟩
      · exact Relation.ReflTransGen.tail ((ih _ hl.2 (by omega)).1 h1) ⟨k, hk, rfl, Or.inr ⟨rfl, h2⟩⟩
    · intro h
      rcases Relation.ReflTransGen.cases_tail h with h | ⟨a, ha, k', hk', hwk, hor⟩
      · omega
      · have hkk : k' = k := by omega
        subst hkk
        rcases hor with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
        · have := (ih _ hl.1 (by omega)).2 ha
          simp [this, hf]
        · have := (ih _ hl.2 (by omega)).2 ha
          simp [this, hf]
