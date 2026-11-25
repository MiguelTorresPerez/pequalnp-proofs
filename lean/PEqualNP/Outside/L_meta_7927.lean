import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7927

open PEqualNP.Defs.LratEncoding PEqualNP.CircuitLowerBounds

theorem litVal_P (a : ℕ → Bool) (v : ℕ) : litVal a (P v) = a (v + 1) := by
  unfold litVal P
  rw [show (2 * v + 2) / 2 = v + 1 by omega, show (2 * v + 2) % 2 = 0 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_Q (a : ℕ → Bool) (v : ℕ) : litVal a (Q v) = !a (v + 1) := by
  unfold litVal Q
  rw [show (2 * v + 3) / 2 = v + 1 by omega, show (2 * v + 3) % 2 = 1 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_L (a : ℕ → Bool) (v : ℕ) (b : Bool) : litVal a (L v b) = (a (v + 1) == b) := by
  cases b <;> simp [L, litVal_P, litVal_Q]

theorem cs_cons (a : ℕ → Bool) (l : ℕ) (c : List ℕ) :
    ClauseSat a (l :: c) ↔ litVal a l = true ∨ ClauseSat a c := by
  simp [ClauseSat]

theorem cs_nil (a : ℕ → Bool) : ClauseSat a [] ↔ False := by simp [ClauseSat]

section ex
variable {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {a : ℕ → Bool}

theorem e_op (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {j : ℕ} (hj : j < s) :
    a (ix n s 0 j 0 + 1) = true ∨ a (ix n s 0 j 1 + 1) = true ∨ a (ix n s 0 j 2 + 1) = true := by
  have hm : [P (ix n s 0 j 0), P (ix n s 0 j 1), P (ix n s 0 j 2)] ∈ fOp n s :=
    List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  have := h _ (by simp only [enc, List.mem_append]; tauto)
  simpa [cs_cons, cs_nil, litVal_P] using this

theorem e_src (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {e j : ℕ} (he : e = 1 ∨ e = 2)
    (hj : j < s) : ∃ k, k ≤ n + j ∧ a (ix n s e j k + 1) = true := by
  have hm : (List.range (n + j + 1)).map (fun k => P (ix n s e j k)) ∈ fSrcAlo n s :=
    List.mem_flatMap.2 ⟨e, by rcases he with rfl | rfl <;> simp,
      List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩
  obtain ⟨l, hl, hv⟩ := h _ (by simp only [enc, List.mem_append]; tauto)
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl
  rw [litVal_P] at hv
  exact ⟨k, by have := List.mem_range.1 hk; omega, hv⟩

theorem e_srcEq (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {e j k r : ℕ} (he : e = 1 ∨ e = 2)
    (hj : j < s) (hr : r ∈ rows) (hk : k ≤ n + j) :
    ∀ c ∈ srcEq n s e j k r, ClauseSat a c := by
  intro c hc
  have hm : c ∈ fSrcEq n s rows :=
    List.mem_flatMap.2 ⟨e, by rcases he with rfl | rfl <;> simp,
      List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, List.mem_flatMap.2 ⟨r, hr,
        List.mem_flatMap.2 ⟨k, List.mem_range.2 (by omega), hc⟩⟩⟩⟩
  exact h _ (by simp only [enc, List.mem_append]; tauto)

theorem e_srcA (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {e j k r : ℕ} (he : e = 1 ∨ e = 2)
    (hj : j < s) (hr : r ∈ rows) (hk : k ≤ n + j) (hb : a (ix n s e j k + 1) = true)
    (hkn : k < n) : a (ix n s (e + 3) j r + 1) = r.testBit k := by
  have := e_srcEq h he hj hr hk [Q (ix n s e j k), L (ix n s (e + 3) j r) (r.testBit k)]
    (by simp [srcEq, hkn])
  simpa [cs_cons, cs_nil, litVal_Q, litVal_L, hb] using this

theorem e_srcB (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {e j k r : ℕ} (he : e = 1 ∨ e = 2)
    (hj : j < s) (hr : r ∈ rows) (hk : k ≤ n + j) (hb : a (ix n s e j k + 1) = true)
    (hkn : n ≤ k) (hkj : k < n + j) :
    a (ix n s (e + 3) j r + 1) = a (ix n s 3 (k - n) r + 1) := by
  have hn : ¬ k < n := by omega
  have h1 := e_srcEq h he hj hr hk
    [Q (ix n s e j k), Q (ix n s (e + 3) j r), P (ix n s 3 (k - n) r)] (by simp [srcEq, hn, hkj])
  have h2 := e_srcEq h he hj hr hk
    [Q (ix n s e j k), P (ix n s (e + 3) j r), Q (ix n s 3 (k - n) r)] (by simp [srcEq, hn, hkj])
  simp only [cs_cons, cs_nil, litVal_Q, litVal_P, hb] at h1 h2
  revert h1 h2
  cases a (ix n s (e + 3) j r + 1) <;> cases a (ix n s 3 (k - n) r + 1) <;> simp

theorem e_srcC (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {e j r : ℕ} (he : e = 1 ∨ e = 2)
    (hj : j < s) (hr : r ∈ rows) (hb : a (ix n s e j (n + j) + 1) = true) :
    a (ix n s (e + 3) j r + 1) = false := by
  have h1 := e_srcEq h he hj hr (le_refl _)
    [Q (ix n s e j (n + j)), Q (ix n s (e + 3) j r)] (by simp [srcEq])
  simpa [cs_cons, cs_nil, litVal_Q, hb] using h1

theorem e_gate (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {j r : ℕ}
    (hj : j < s) (hr : r ∈ rows) :
    (a (ix n s 0 j 0 + 1) = true →
      a (ix n s 3 j r + 1) = (a (ix n s 4 j r + 1) && a (ix n s 5 j r + 1))) ∧
    (a (ix n s 0 j 1 + 1) = true →
      a (ix n s 3 j r + 1) = (a (ix n s 4 j r + 1) || a (ix n s 5 j r + 1))) ∧
    (a (ix n s 0 j 2 + 1) = true → a (ix n s 3 j r + 1) = true) := by
  have hg : ∀ c ∈ gateCl n s j r, ClauseSat a c := by
    intro c hc
    have hm : c ∈ fGate n s rows :=
      List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, List.mem_flatMap.2 ⟨r, hr, hc⟩⟩
    exact h _ (by simp only [enc, List.mem_append]; tauto)
  simp only [gateCl, List.forall_mem_cons, List.not_mem_nil, cs_cons, cs_nil, litVal_Q,
    litVal_P] at hg
  revert hg
  cases a (ix n s 0 j 0 + 1) <;> cases a (ix n s 0 j 1 + 1) <;> cases a (ix n s 0 j 2 + 1) <;>
    cases a (ix n s 3 j r + 1) <;> cases a (ix n s 4 j r + 1) <;>
    cases a (ix n s 5 j r + 1) <;> simp

theorem e_out (h : ∀ c ∈ enc n s g rows, ClauseSat a c) :
    ∃ k, k ≤ n + s ∧ a (ix n s 6 0 k + 1) = true := by
  have hm : (List.range (n + s + 1)).map (fun k => P (ix n s 6 0 k)) ∈ fOutAlo n s := by
    simp [fOutAlo]
  obtain ⟨l, hl, hv⟩ := h _ (by simp only [enc, List.mem_append]; tauto)
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl
  rw [litVal_P] at hv
  exact ⟨k, by have := List.mem_range.1 hk; omega, hv⟩

theorem e_outEq (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {k r : ℕ}
    (hr : r ∈ rows) (hk : k ≤ n + s) :
    ∀ c ∈ outEq n s g k r, ClauseSat a c := by
  intro c hc
  have hm : c ∈ fOutEq n s g rows :=
    List.mem_flatMap.2 ⟨r, hr, List.mem_flatMap.2 ⟨k, List.mem_range.2 (by omega), hc⟩⟩
  exact h _ (by simp only [enc, List.mem_append]; tauto)

theorem e_outA (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {k r : ℕ}
    (hr : r ∈ rows) (hk : k ≤ n + s) (hb : a (ix n s 6 0 k + 1) = true) (hkn : k < n) :
    r.testBit k = g r := by
  by_contra hne
  have := e_outEq h hr hk [Q (ix n s 6 0 k)] (by simp [outEq, hkn, hne])
  simp [cs_cons, cs_nil, litVal_Q, hb] at this

theorem e_outB (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {k r : ℕ}
    (hr : r ∈ rows) (hk : k ≤ n + s) (hb : a (ix n s 6 0 k + 1) = true) (hkn : n ≤ k)
    (hks : k < n + s) : a (ix n s 3 (k - n) r + 1) = g r := by
  have hn : ¬ k < n := by omega
  have := e_outEq h hr hk [Q (ix n s 6 0 k), L (ix n s 3 (k - n) r) (g r)]
    (by simp [outEq, hn, hks])
  simpa [cs_cons, cs_nil, litVal_Q, litVal_L, hb] using this

theorem e_outC (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {r : ℕ}
    (hr : r ∈ rows) (hb : a (ix n s 6 0 (n + s) + 1) = true) : g r = false := by
  by_contra hne
  have hg : g r = true := by simpa using hne
  have := e_outEq h hr (le_refl _) [Q (ix n s 6 0 (n + s))] (by simp [outEq, hg])
  simp [cs_cons, cs_nil, litVal_Q, hb] at this

end ex

theorem main (n s : ℕ) (x1 : ℕ → Bool) (x2 : List ℕ) (hsat : FormulaSat (enc n s x1 x2)) :
    ∃ (x4 : ℕ → ℕ → Bool),
      (∀ x6 < s, (∀ x8 ∈ x2, x4 x6 x8 = true) ∨ ∃ (x8 : ℕ) (x9 : ℕ),
        (∀ x10 ∈ x2, x4 x6 x10 =
          ((fun (x5 x6 x7 : ℕ) => if x6 < n then x7.testBit x6 else if x6 < n + x5 then x4 (x6 - n) x7 else false) x6 x8 x10 &&
           (fun (x5 x6 x7 : ℕ) => if x6 < n then x7.testBit x6 else if x6 < n + x5 then x4 (x6 - n) x7 else false) x6 x9 x10)) ∨
        ∀ x10 ∈ x2, x4 x6 x10 =
          ((fun (x5 x6 x7 : ℕ) => if x6 < n then x7.testBit x6 else if x6 < n + x5 then x4 (x6 - n) x7 else false) x6 x8 x10 ||
           (fun (x5 x6 x7 : ℕ) => if x6 < n then x7.testBit x6 else if x6 < n + x5 then x4 (x6 - n) x7 else false) x6 x9 x10)) ∧
      ∃ (x6 : ℕ), ∀ x7 ∈ x2,
        (fun (x5 x6 x7 : ℕ) => if x6 < n then x7.testBit x6 else if x6 < n + x5 then x4 (x6 - n) x7 else false) s x6 x7 = x1 x7 := by
  obtain ⟨a, h⟩ := hsat
  refine ⟨fun j r => a (ix n s 3 j r + 1), ?_, ?_⟩
  · intro j hj
    have hu : ∀ e : ℕ, e = 1 ∨ e = 2 → ∃ k, ∀ r ∈ x2, a (ix n s (e + 3) j r + 1) =
        (if k < n then r.testBit k else if k < n + j then a (ix n s 3 (k - n) r + 1) else false) := by
      intro e he
      obtain ⟨k, hk, hb⟩ := e_src h he hj
      refine ⟨k, fun r hr => ?_⟩
      by_cases hkn : k < n
      · rw [if_pos hkn, e_srcA h he hj hr hk hb hkn]
      · rw [if_neg hkn]
        by_cases hkj : k < n + j
        · rw [if_pos hkj, e_srcB h he hj hr hk hb (by omega) hkj]
        · rw [if_neg hkj]
          have he2 : k = n + j := by omega
          rw [he2] at hb
          exact e_srcC h he hj hr hb
    obtain ⟨k1, hk1⟩ := hu 1 (Or.inl rfl)
    obtain ⟨k2, hk2⟩ := hu 2 (Or.inr rfl)
    rcases e_op h hj with c | c | c
    · right
      refine ⟨k1, k2, Or.inl fun r hr => ?_⟩
      have := (e_gate (g := x1) h hj hr).1 c
      beta_reduce
      rw [this, hk1 r hr, hk2 r hr]
    · right
      refine ⟨k1, k2, Or.inr fun r hr => ?_⟩
      have := (e_gate (g := x1) h hj hr).2.1 c
      beta_reduce
      rw [this, hk1 r hr, hk2 r hr]
    · left
      intro r hr
      exact (e_gate (g := x1) h hj hr).2.2 c
  · obtain ⟨ko, hko, hbo⟩ := e_out h
    refine ⟨ko, fun r hr => ?_⟩
    show (if ko < n then r.testBit ko else if ko < n + s then a (ix n s 3 (ko - n) r + 1) else false) = x1 r
    by_cases hkn : ko < n
    · rw [if_pos hkn]; exact e_outA h hr hko hbo hkn
    · rw [if_neg hkn]
      by_cases hks : ko < n + s
      · rw [if_pos hks]; exact e_outB h hr hko hbo (by omega) hks
      · rw [if_neg hks]
        have he2 : ko = n + s := by omega
        rw [he2] at hbo
        exact (e_outC h hr hbo).symm

theorem main2 (x1 : ℕ → Bool) (x2 : List ℕ) (hsat : FormulaSat (enc2 14 26 x1 x2)) :
    FormulaSat (enc 14 26 x1 x2) := by
  obtain ⟨a, h⟩ := hsat
  exact ⟨a, fun c hc => h c (List.mem_append_left _ hc)⟩

end PEqualNP.Outside.L_meta_7927

theorem PEqualNP.Outside.L_meta_7927 : ∀ (x1 : ℕ → Bool) (x2 : List ℕ),   PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc2 (14 : ℕ) (26 : ℕ) x1 x2) →     ∃ (x4 : ℕ → ℕ → Bool),       have x5 : ℕ → ℕ → ℕ → Bool := fun (x5 x6 x7 : ℕ) => if x6 < (14 : ℕ) then x7.testBit x6 else if x6 < (14 : ℕ) + x5 then x4 (x6 - (14 : ℕ)) x7 else Bool.false;       (∀ x6 < (26 : ℕ), (∀ x8 ∈ x2, x4 x6 x8 = Bool.true) ∨ ∃ (x8 : ℕ) (x9 : ℕ), (∀ x10 ∈ x2, x4 x6 x10 = (x5 x6 x8 x10 && x5 x6 x9 x10)) ∨ ∀ x10 ∈ x2, x4 x6 x10 = (x5 x6 x8 x10 || x5 x6 x9 x10)) ∧ ∃ (x6 : ℕ), ∀ x7 ∈ x2, x5 (26 : ℕ) x6 x7 = x1 x7 :=
  fun x1 x2 h => PEqualNP.Outside.L_meta_7927.main 14 26 x1 x2 (PEqualNP.Outside.L_meta_7927.main2 x1 x2 h)
