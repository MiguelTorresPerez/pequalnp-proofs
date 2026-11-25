import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5549

open PEqualNP.CircuitLowerBounds in
theorem noGate (o : ℕ)
    (hr : PEqualNP.Represents.Represents (fun u v : Fin 4 => (4383 : ℕ).testBit (4 * u.val + v.val))
      ({ gates := [], output := o } : Circuit)) : False := by
  have h1 := hr 0 0
  have h2 := hr 0 1
  have h3 := hr 1 0
  simp only [Circuit.eval, Circuit.wires, List.foldl_nil] at h1 h2 h3
  rcases o with _ | _ | _ | _ | _ | _ | _ | _ | o
  · first | (revert h1; decide) | (revert h2; decide) | (revert h3; decide)
  · first | (revert h1; decide) | (revert h2; decide) | (revert h3; decide)
  · first | (revert h1; decide) | (revert h2; decide) | (revert h3; decide)
  · first | (revert h1; decide) | (revert h2; decide) | (revert h3; decide)
  · first | (revert h1; decide) | (revert h2; decide) | (revert h3; decide)
  · first | (revert h1; decide) | (revert h2; decide) | (revert h3; decide)
  · first | (revert h1; decide) | (revert h2; decide) | (revert h3; decide)
  · first | (revert h1; decide) | (revert h2; decide) | (revert h3; decide)
  · have hl : (PEqualNP.Represents.oneEach (0 : Fin 4) (0 : Fin 4)).length ≤ o + 8 := by
      simp [PEqualNP.Represents.oneEach]
    rw [List.getD_eq_default _ _ hl] at h1
    revert h1; decide

end PEqualNP.Outside.L_meta_5549

theorem PEqualNP.Outside.L_meta_5549 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4383 : ℕ).testBit (4 * u.val + v.val)) 1 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4383 : ℕ).testBit (4 * u.val + v.val)) 0 := by
  refine ⟨⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }], output := 8 }, ?_, by decide, by decide +kernel⟩, ?_⟩
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩
  · rintro ⟨⟨gs, o⟩, -, hs, hr⟩
    have hg : gs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hs)
    subst hg
    exact PEqualNP.Outside.L_meta_5549.noGate o hr
