import Mathlib
import PEqualNP.Defs
import PEqualNP.Gct.L065
import PEqualNP.Gct.Helpers.FermatFromKneser

open Module Finset PEqualNP.Gct.Helpers

namespace PEqualNP.Outside.L_gct_122

-- The polarized hypotheses: W is isotropic for the dot product and for the
-- four-linear form given by the sum of u_i v_i z_i y_i.
def Iso4 {ι : Type} [Fintype ι] (W : Submodule ℂ (ι → ℂ)) : Prop :=
  (∀ u ∈ W, ∀ v ∈ W, ∑ i, u i * v i = 0) ∧
    (∀ u ∈ W, ∀ v ∈ W, ∀ z ∈ W, ∀ y ∈ W, ∑ i, u i * v i * z i * y i = 0)

section General

variable {ι : Type} [Fintype ι]

-- Every element of W * W has coordinate sum zero.
theorem sum_eq_zero_of_mem_mul {W : Submodule ℂ (ι → ℂ)} (hW : Iso4 W) :
    ∀ a ∈ W * W, ∑ i, a i = 0 := by
  intro a ha
  refine Submodule.mul_induction_on ha ?_ ?_
  · intro m hm n hn
    simpa only [Pi.mul_apply] using hW.1 m hm n hn
  · intro a b ha hb
    simp only [Pi.add_apply, sum_add_distrib, ha, hb, add_zero]

-- W * W is isotropic for the dot product.
theorem dot_eq_zero_of_mem_mul {W : Submodule ℂ (ι → ℂ)} (hW : Iso4 W) :
    ∀ a ∈ W * W, ∀ b ∈ W * W, ∑ i, a i * b i = 0 := by
  intro a ha
  refine Submodule.mul_induction_on ha ?_ ?_
  · intro m hm n hn b hb
    refine Submodule.mul_induction_on hb ?_ ?_
    · intro z hz y hy
      have := hW.2 m hm n hn z hz y hy
      calc ∑ i, (m * n) i * (z * y) i = ∑ i, m i * n i * z i * y i := by
            refine sum_congr rfl fun i _ => ?_
            simp only [Pi.mul_apply]; ring
        _ = 0 := this
    · intro c d hc hd
      simp only [Pi.add_apply, mul_add, sum_add_distrib, hc, hd, add_zero]
  · intro a a' ha ha' b hb
    simp only [Pi.add_apply, add_mul, sum_add_distrib, ha b hb, ha' b hb, add_zero]

-- Restricting along a 0/1 element of the stabilizer of W * W keeps the hypotheses.
theorem restr_iso4 {W : Submodule ℂ (ι → ℂ)} (hW : Iso4 W) {p : ι → ℂ}
    (hp : p ∈ stab (W * W)) (hp01 : ∀ k, p k = 0 ∨ p k = 1) :
    Iso4 (W.map (restr p)) := by
  constructor
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [restr_apply]
    rw [sum_restr p hp01 (fun k => u k * v k)]
    have := sum_eq_zero_of_mem_mul hW _ (hp _ (Submodule.mul_mem_mul hu hv))
    simpa only [Pi.mul_apply, mul_assoc] using this
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ _ ⟨z, hz, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [restr_apply]
    rw [sum_restr p hp01 (fun k => u k * v k * z k * y k)]
    have := dot_eq_zero_of_mem_mul hW _ (hp _ (Submodule.mul_mem_mul hu hv)) _
      (Submodule.mul_mem_mul hz hy)
    calc ∑ k, p k * (u k * v k * z k * y k)
        = ∑ k, (p * (u * v)) k * (z * y) k := by
          refine sum_congr rfl fun k _ => ?_
          simp only [Pi.mul_apply]; ring
      _ = 0 := this

end General

-- The bound for polarized hypotheses on any finite index type, given Kneser.
theorem quartic_general (hK : ∀ (ι : Type) [Fintype ι], KneserFor ι) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι], Fintype.card ι = n →
      ∀ W : Submodule ℂ (ι → ℂ), Iso4 W → 3 * finrank ℂ W ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ι _ hcard W hW
  classical
  by_cases hW0 : W = ⊥
  · rw [hW0, finrank_bot]; omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hu0
  have : Nonempty ι := ⟨i₀⟩
  set V := W * W with hVdef
  by_cases hconst : ∀ x ∈ stab V, ∀ j k, x j = x k
  · -- the stabilizer is the scalars: apply Kneser to W and W
    have hSt : finrank ℂ (stab V) ≤ 1 := by
      have : stab V ≤ Submodule.span ℂ {(1 : ι → ℂ)} := by
        intro x hx
        rw [Submodule.mem_span_singleton]
        refine ⟨x i₀, ?_⟩
        funext k
        simp [hconst x hx i₀ k]
      exact (Submodule.finrank_mono this).trans (finrank_span_singleton one_ne_zero).le
    have hone : (1 : ι → ℂ) ∉ V := by
      intro h
      have := dot_eq_zero_of_mem_mul hW 1 h 1 h
      simp only [Pi.one_apply, mul_one, sum_const, card_univ, nsmul_eq_mul] at this
      exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 this)
    have hU : finrank ℂ ↥(V ⊔ Submodule.span ℂ {(1 : ι → ℂ)}) = finrank ℂ V + 1 := by
      have hinf : V ⊓ Submodule.span ℂ {(1 : ι → ℂ)} = ⊥ := by
        rw [eq_bot_iff]
        intro x ⟨hxV, hx1⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx1
        rw [Submodule.mem_bot]
        by_contra hc
        have hc' : c ≠ 0 := by rintro rfl; exact hc (zero_smul _ _)
        apply hone
        have := V.smul_mem c⁻¹ hxV
        rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
      have h := Submodule.finrank_sup_add_finrank_inf_eq V (Submodule.span ℂ {(1 : ι → ℂ)})
      rw [hinf, finrank_bot, add_zero,
        finrank_span_singleton (one_ne_zero : (1 : ι → ℂ) ≠ 0)] at h
      exact h
    have hperp : ∀ v ∈ V, ∀ z ∈ V ⊔ Submodule.span ℂ {(1 : ι → ℂ)}, ∑ i, v i * z i = 0 := by
      intro v hv z hz
      obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      have h1 := dot_eq_zero_of_mem_mul hW v hv a ha
      have h2 := sum_eq_zero_of_mem_mul hW v hv
      calc ∑ i, v i * (a + c • (1 : ι → ℂ)) i = ∑ i, v i * a i + c * ∑ i, v i := by
            rw [mul_sum, ← sum_add_distrib]
            refine sum_congr rfl fun i _ => ?_
            simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
            ring
        _ = 0 := by rw [h1, h2, mul_zero, add_zero]
    have hp := perp_bound V (V ⊔ Submodule.span ℂ {(1 : ι → ℂ)}) hperp
    have hk := hK ι W W (stab V) hW0 hW0 (fun x => Iff.rfl)
    change _ + _ ≤ finrank ℂ V + _ at hk
    rw [hU, hcard] at hp
    omega
  · push Not at hconst
    obtain ⟨x, hx, j, k, hjk⟩ := hconst
    obtain ⟨e, he, hev⟩ := exists_indicator hx j
    have he01 : ∀ l, e l = 0 ∨ e l = 1 := fun l => by
      rw [hev l]; split_ifs <;> simp
    set f : ι → ℂ := 1 - e with hf
    have hfS : f ∈ stab V := (stab V).sub_mem (one_mem_stab V) he
    have hf01 : ∀ l, f l = 0 ∨ f l = 1 := fun l => by
      rcases he01 l with h | h <;> simp [hf, h]
    have hej : e j = 1 := by rw [hev]; simp
    have hek : e k = 0 := by rw [hev]; simp [Ne.symm hjk]
    have hcB : Fintype.card {l // e l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := k) (by rw [hek]; exact zero_ne_one)
    have hcB' : Fintype.card {l // f l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := j) (by simp [hf, hej])
    have hsum : Fintype.card {l // e l = 1} + Fintype.card {l // f l = 1} ≤ n := by
      rw [Fintype.card_subtype, Fintype.card_subtype, ← hcard,
        ← Finset.card_union_of_disjoint]
      · exact Finset.card_le_univ _
      · rw [Finset.disjoint_filter]
        intro l _ h1 h2
        simp [hf, h1] at h2
    have h1 := IH _ hcB {l // e l = 1} rfl _ (restr_iso4 hW he he01)
    have h2 := IH _ hcB' {l // f l = 1} rfl _ (restr_iso4 hW hfS hf01)
    have h3 := finrank_split W e f (fun l => by
      rcases he01 l with h | h
      · right; simp [hf, h]
      · left; exact h)
    omega

end PEqualNP.Outside.L_gct_122

theorem PEqualNP.Outside.L_gct_122 : ∀ (m : ℕ) (X : Submodule ℂ (Fin m → ℂ)), (∀ x ∈ X, ∑ i, x i ^ 2 = 0) → (∀ x ∈ X, ∑ i, x i ^ 4 = 0) → 3 * Module.finrank ℂ X ≤ m := by
  intro M W h2 h4
  have hQ : ∀ u ∈ W, ∀ v ∈ W, ∑ i, u i * v i = 0 := by
    intro u hu v hv
    have key : ∑ i, (2 : ℂ) * (u i * v i) =
        (∑ i, (u + v) i ^ 2) - (∑ i, u i ^ 2) - (∑ i, v i ^ 2) := by
      simp only [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    rw [h2 _ (W.add_mem hu hv), h2 u hu, h2 v hv, ← Finset.mul_sum] at key
    simpa using key
  have hC : ∀ u ∈ W, ∀ v ∈ W, ∀ z ∈ W, ∀ y ∈ W, ∑ i, u i * v i * z i * y i = 0 := by
    intro a ha b hb c hc d hd
    have key : ∑ i, (24 : ℂ) * (a i * b i * c i * d i) =
        (∑ i, (a + b + c + d) i ^ 4)
          - (∑ i, (a + b + c) i ^ 4) - (∑ i, (a + b + d) i ^ 4)
          - (∑ i, (a + c + d) i ^ 4) - (∑ i, (b + c + d) i ^ 4)
          + (∑ i, (a + b) i ^ 4) + (∑ i, (a + c) i ^ 4) + (∑ i, (a + d) i ^ 4)
          + (∑ i, (b + c) i ^ 4) + (∑ i, (b + d) i ^ 4) + (∑ i, (c + d) i ^ 4)
          - (∑ i, a i ^ 4) - (∑ i, b i ^ 4) - (∑ i, c i ^ 4) - (∑ i, d i ^ 4) := by
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    have m3 := fun x (hx : x ∈ W) y (hy : y ∈ W) z (hz : z ∈ W) =>
      W.add_mem (W.add_mem hx hy) hz
    rw [h4 _ (W.add_mem (m3 a ha b hb c hc) hd),
      h4 _ (m3 a ha b hb c hc), h4 _ (m3 a ha b hb d hd), h4 _ (m3 a ha c hc d hd),
      h4 _ (m3 b hb c hc d hd),
      h4 _ (W.add_mem ha hb), h4 _ (W.add_mem ha hc), h4 _ (W.add_mem ha hd),
      h4 _ (W.add_mem hb hc), h4 _ (W.add_mem hb hd), h4 _ (W.add_mem hc hd),
      h4 a ha, h4 b hb, h4 c hc, h4 d hd, ← Finset.mul_sum] at key
    have h24 : (24 : ℂ) ≠ 0 := by norm_num
    simpa [h24] using key
  exact PEqualNP.Outside.L_gct_122.quartic_general
    (kneserFor_of_fin PEqualNP.Gct.L065) M (Fin M) (Fintype.card_fin M) W ⟨hQ, hC⟩
