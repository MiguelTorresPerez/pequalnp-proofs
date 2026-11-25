import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8195

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

lemma W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs a ih => rw [W_snoc]; simp [ih]; omega

lemma W_pre (gs : List Gate) (x : List Bool) : ∀ (hs : List Gate) (i : ℕ),
    i < x.length + gs.length → (W (gs ++ hs) x).getD i false = (W gs x).getD i false := by
  intro hs
  induction hs using List.reverseRecOn with
  | nil => intro i _; simp
  | append_singleton hs a ih =>
    intro i hi
    rw [← List.append_assoc, W_snoc, List.getD_append _ _ _ _ (by rw [W_length]; simp; omega)]
    exact ih i hi

def val (gs : List Gate) (x : List Bool) (v : ℕ) : Bool := (W gs x).getD v false

section
variable {X Y : Type} (x1 : ℕ) (x6 : Y → Fin x1 → Bool) (x7 : ℕ → Set (X × Y)) (a b : ℕ → ℕ)

open Classical in
noncomputable def step (gs : List Gate) (k : ℕ) : Gate :=
  if (∃ pq ∈ x7 (x1 + k), val gs (List.ofFn (x6 pq.2)) (a k) = true) ∧
     (∃ pq ∈ x7 (x1 + k), val gs (List.ofFn (x6 pq.2)) (b k) = true) then ⟨GateOp.and, [a k, b k]⟩
  else if (∃ pq ∈ x7 (x1 + k), val gs (List.ofFn (x6 pq.2)) (b k) = true) then ⟨GateOp.or, [a k]⟩
  else if (∃ pq ∈ x7 (x1 + k), val gs (List.ofFn (x6 pq.2)) (a k) = true) then ⟨GateOp.or, [b k]⟩
  else ⟨GateOp.or, [a k, b k]⟩

noncomputable def gsq : ℕ → List Gate
  | 0 => []
  | k + 1 => gsq k ++ [step x1 x6 x7 a b (gsq k) k]

lemma step_ok (gs : List Gate) (k : ℕ) :
    (step x1 x6 x7 a b gs k).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
    (step x1 x6 x7 a b gs k).inputs.length ≤ 2 := by
  unfold step
  split_ifs <;> simp

lemma gsq_ok (k : ℕ) : ∀ g ∈ gsq x1 x6 x7 a b k,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction k with
  | zero => simp [gsq]
  | succ k ih =>
    intro g hg
    simp only [gsq, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact ih g hg
    · subst hg; exact step_ok x1 x6 x7 a b _ k

lemma gsq_length (k : ℕ) : (gsq x1 x6 x7 a b k).length = k := by
  induction k with
  | zero => simp [gsq]
  | succ k ih => simp [gsq, ih]

lemma gsq_prefix (k d : ℕ) : ∃ t, gsq x1 x6 x7 a b (k + d) = gsq x1 x6 x7 a b k ++ t := by
  induction d with
  | zero => exact ⟨[], by simp⟩
  | succ d ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t ++ [step x1 x6 x7 a b (gsq x1 x6 x7 a b (k + d)) (k + d)], ?_⟩
    rw [← Nat.add_assoc, gsq, ht, List.append_assoc]

lemma stab (x2 k w : ℕ) (x : List Bool) (hk : k ≤ x2) (hw : w < x1 + k) (hx : x.length = x1) :
    val (gsq x1 x6 x7 a b k) x w = val (gsq x1 x6 x7 a b x2) x w := by
  obtain ⟨t, ht⟩ := gsq_prefix x1 x6 x7 a b k (x2 - k)
  have e : k + (x2 - k) = x2 := by omega
  rw [e] at ht
  unfold val
  rw [ht, W_pre _ x t w (by rw [gsq_length, hx]; exact hw)]

lemma gate (x2 k : ℕ) (x : List Bool) (hk : k < x2) (hx : x.length = x1) :
    val (gsq x1 x6 x7 a b x2) x (x1 + k) =
      (step x1 x6 x7 a b (gsq x1 x6 x7 a b k) k).op.eval
        ((step x1 x6 x7 a b (gsq x1 x6 x7 a b k) k).inputs.map (val (gsq x1 x6 x7 a b k) x)) := by
  rw [← stab x1 x6 x7 a b x2 (k + 1) (x1 + k) x (by omega) (by omega) hx]
  unfold val
  rw [gsq, W_snoc, List.getD_append_right _ _ _ _ (by rw [W_length, gsq_length, hx])]
  rw [W_length, gsq_length, hx, Nat.sub_self]
  rfl

lemma input (x2 v : ℕ) (f : Fin x1 → Bool) (hv : v < x1) :
    val (gsq x1 x6 x7 a b x2) (List.ofFn f) v = f ⟨v, hv⟩ := by
  have := W_pre [] (List.ofFn f) (gsq x1 x6 x7 a b x2) v (by simpa using hv)
  unfold val
  simp only [List.nil_append] at this
  rw [this]
  simp [W, hv]

end

theorem main {X Y : Type} (x1 x2 : ℕ) (x5 : X → Fin x1 → Bool) (x6 : Y → Fin x1 → Bool)
    (x7 : ℕ → Set (X × Y)) (a b : ℕ → ℕ)
    (H1 : ∀ (x8 : Fin x1), ∀ x9 ∈ x7 ↑x8, x5 x9.1 x8 = true ∧ x6 x9.2 x8 = false)
    (Hp : ∀ k < x2, ∀ p ∈ x7 (x1 + k), ∀ q ∈ x7 (x1 + k), (p.1, q.2) ∈ x7 (x1 + k))
    (Ha : ∀ k < x2, a k < x1 + k) (Hb : ∀ k < x2, b k < x1 + k)
    (Hs : ∀ k < x2, x7 (x1 + k) ⊆ x7 (a k) ∪ x7 (b k)) :
    ∀ w, w < x1 + x2 → ∀ pq ∈ x7 w,
      val (gsq x1 x6 x7 a b x2) (List.ofFn (x5 pq.1)) w = true ∧
      val (gsq x1 x6 x7 a b x2) (List.ofFn (x6 pq.2)) w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw pq hpq
    by_cases hin : w < x1
    · rw [input x1 x6 x7 a b x2 w _ hin, input x1 x6 x7 a b x2 w _ hin]
      exact H1 ⟨w, hin⟩ pq hpq
    obtain ⟨k, rfl⟩ : ∃ k, w = x1 + k := ⟨w - x1, by omega⟩
    have hk : k < x2 := by omega
    rw [gate x1 x6 x7 a b x2 k _ hk (by simp), gate x1 x6 x7 a b x2 k _ hk (by simp)]
    set V := val (gsq x1 x6 x7 a b x2) with hV
    have hA := Ha k hk
    have hB := Hb k hk
    have ihA := ih (a k) hA (by omega)
    have ihB := ih (b k) hB (by omega)
    have hS := Hs k hk
    have hP := Hp k hk
    have sA : ∀ (x : List Bool), x.length = x1 →
        val (gsq x1 x6 x7 a b k) x (a k) = V x (a k) := fun x hx =>
      stab x1 x6 x7 a b x2 k (a k) x hk.le hA hx
    have sB : ∀ (x : List Bool), x.length = x1 →
        val (gsq x1 x6 x7 a b k) x (b k) = V x (b k) := fun x hx =>
      stab x1 x6 x7 a b x2 k (b k) x hk.le hB hx
    -- key fact
    have keyA : ∀ r ∈ x7 (x1 + k), V (List.ofFn (x6 r.2)) (a k) = true →
        ∀ s ∈ x7 (x1 + k), V (List.ofFn (x5 s.1)) (b k) = true := by
      intro r hr hra s hs
      have hm := hS (hP s hs r hr)
      rcases hm with hm | hm
      · have := (ihA _ hm).2; simp at this; rw [this] at hra; exact absurd hra (by simp)
      · exact (ihB _ hm).1
    have keyB : ∀ r ∈ x7 (x1 + k), V (List.ofFn (x6 r.2)) (b k) = true →
        ∀ s ∈ x7 (x1 + k), V (List.ofFn (x5 s.1)) (a k) = true := by
      intro r hr hrb s hs
      have hm := hS (hP s hs r hr)
      rcases hm with hm | hm
      · exact (ihA _ hm).1
      · have := (ihB _ hm).2; simp at this; rw [this] at hrb; exact absurd hrb (by simp)
    have pA := ihA pq
    have pB := ihB pq
    have hpS := hS hpq
    unfold step
    split_ifs with h1 h2 h3
    · obtain ⟨⟨r, hr, hra⟩, ⟨r', hr', hrb⟩⟩ := h1
      rw [sA _ (by simp)] at hra
      rw [sB _ (by simp)] at hrb
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id, Bool.and_true]
      rw [sA _ (by simp), sB _ (by simp), sA _ (by simp), sB _ (by simp)]
      refine ⟨by rw [keyB r' hr' hrb pq hpq, keyA r hr hra pq hpq]; rfl, ?_⟩
      rcases hpS with hm | hm
      · rw [(ihA _ hm).2]; rfl
      · rw [(ihB _ hm).2]; simp
    · obtain ⟨r, hr, hrb⟩ := h2
      rw [sB _ (by simp)] at hrb
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id, Bool.or_false]
      rw [sA _ (by simp), sA _ (by simp)]
      refine ⟨keyB r hr hrb pq hpq, ?_⟩
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      apply h1
      refine ⟨⟨pq, hpq, by rw [sA _ (by simp)]; exact hc⟩, ⟨r, hr, by rw [sB _ (by simp)]; exact hrb⟩⟩
    · obtain ⟨r, hr, hra⟩ := h3
      rw [sA _ (by simp)] at hra
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id, Bool.or_false]
      rw [sB _ (by simp), sB _ (by simp)]
      refine ⟨keyA r hr hra pq hpq, ?_⟩
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      exact h2 ⟨pq, hpq, by rw [sB _ (by simp)]; exact hc⟩
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id, Bool.or_false]
      rw [sA _ (by simp), sB _ (by simp), sA _ (by simp), sB _ (by simp)]
      have nA : V (List.ofFn (x6 pq.2)) (a k) = false := by
        by_contra hc
        simp only [Bool.not_eq_false] at hc
        exact h3 ⟨pq, hpq, by rw [sA _ (by simp)]; exact hc⟩
      have nB : V (List.ofFn (x6 pq.2)) (b k) = false := by
        by_contra hc
        simp only [Bool.not_eq_false] at hc
        exact h2 ⟨pq, hpq, by rw [sB _ (by simp)]; exact hc⟩
      refine ⟨?_, by rw [nA, nB]; rfl⟩
      rcases hpS with hm | hm
      · rw [(ihA _ hm).1]; rfl
      · rw [(ihB _ hm).1]; simp

end PEqualNP.Outside.L_meta_8195

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_8195 in
theorem PEqualNP.Outside.L_meta_8195 : ∀ (x1 x2 : ℕ) (x3 x4 : Type) (x5 : x3 → Fin x1 → Bool) (x6 : x4 → Fin x1 → Bool) (x7 : ℕ → Set (x3 × x4)), (∀ (x8 : Fin x1), ∀ x9 ∈ x7 ↑x8, x5 x9.1 x8 = Bool.true ∧ x6 x9.2 x8 = Bool.false) → (∀ x9 < x2, (∀ x11 ∈ x7 (x1 + x9), ∀ x13 ∈ x7 (x1 + x9), (x11.1, x13.2) ∈ x7 (x1 + x9)) ∧ ∃ x11 < x1 + x9, ∃ x12 < x1 + x9, x7 (x1 + x9) ⊆ x7 x11 ∪ x7 x12) → ∀ x10 < x1 + x2, ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ x12.size ≤ x2 ∧ ∀ x13 ∈ x7 x10, x12.eval (List.ofFn (x5 x13.1)) = Bool.true ∧ x12.eval (List.ofFn (x6 x13.2)) = Bool.false := by
  intro x1 x2 X Y x5 x6 x7 H1 H2 x10 hx10
  have H' : ∀ k, ∃ a b : ℕ, k < x2 → a < x1 + k ∧ b < x1 + k ∧ x7 (x1 + k) ⊆ x7 a ∪ x7 b := by
    intro k
    by_cases hk : k < x2
    · obtain ⟨_, a, ha, b, hb, hs⟩ := H2 k hk
      exact ⟨a, b, fun _ => ⟨ha, hb, hs⟩⟩
    · exact ⟨0, 0, fun h => absurd h hk⟩
  choose a b hab using H'
  refine ⟨⟨gsq x1 x6 x7 a b x2, x10⟩, ?_, ?_, ?_⟩
  · exact gsq_ok x1 x6 x7 a b x2
  · simp [Circuit.size, gsq_length]
  · intro pq hpq
    exact main x1 x2 x5 x6 x7 a b H1 (fun k hk => (H2 k hk).1) (fun k hk => (hab k hk).1)
      (fun k hk => (hab k hk).2.1) (fun k hk => (hab k hk).2.2) x10 hx10 pq hpq
