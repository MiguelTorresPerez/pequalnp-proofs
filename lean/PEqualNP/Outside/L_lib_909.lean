import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_909
theorem s_erase (L : List ℕ) (a t : ℕ) (h : a ∈ L) :
    (L.map (fun v => t - v)).sum = (t - a) + ((L.erase a).map (fun v => t - v)).sum := by
  have hp := (List.perm_cons_erase h).map (fun v => t - v)
  have hs : (L.map (fun v => t - v)).sum = ((a :: L.erase a).map (fun v => t - v)).sum := by
    exact hp.sum_eq
  rw [hs]
  simp only [List.map_cons, List.sum_cons]
theorem s_pos (L : List ℕ) (t : ℕ) : 0 < (L.map (fun v => t - v)).sum → ∃ v ∈ L, v < t := by
  induction L with
  | nil => intro h; simp at h
  | cons x L ih =>
    intro h
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hx : x < t
    · exact ⟨x, by simp, hx⟩
    · obtain ⟨v, hv, hvt⟩ := ih (by omega)
      exact ⟨v, by simp [hv], hvt⟩
theorem s_slope (L : List ℕ) (s : ℕ) :
    (L.map (fun v => (s + 1) - v)).sum
      = (L.map (fun v => s - v)).sum + (L.filter (fun v => decide (v < s + 1))).length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    by_cases h : x < s + 1
    · have e : (x :: L).filter (fun v => decide (v < s + 1))
          = x :: L.filter (fun v => decide (v < s + 1)) :=
        List.filter_cons_of_pos (by simpa using h)
      rw [e]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
    · have e : (x :: L).filter (fun v => decide (v < s + 1))
          = L.filter (fun v => decide (v < s + 1)) :=
        List.filter_cons_of_neg (by simpa using h)
      rw [e]
      simp only [List.map_cons, List.sum_cons]
      omega
theorem s_split_le (L : List ℕ) (t c : ℕ) (htc : t ≤ c) :
    (L.map (fun v => t - v)).sum + (L.filter (fun v => decide (v < t))).length * (c - t)
      ≤ (L.map (fun v => c - v)).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    by_cases h : x < t
    · have e : (x :: L).filter (fun v => decide (v < t))
          = x :: L.filter (fun v => decide (v < t)) :=
        List.filter_cons_of_pos (by simpa using h)
      rw [e]
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · have e : (x :: L).filter (fun v => decide (v < t))
          = L.filter (fun v => decide (v < t)) :=
        List.filter_cons_of_neg (by simpa using h)
      rw [e]
      simp only [List.map_cons, List.sum_cons]
      omega
theorem s_split_eq (L : List ℕ) (t c : ℕ) (htc : t ≤ c) :
    (∀ v ∈ L, v < t ∨ c ≤ v) →
    (L.map (fun v => c - v)).sum
      = (L.map (fun v => t - v)).sum + (L.filter (fun v => decide (v < t))).length * (c - t) := by
  induction L with
  | nil => intro _; simp
  | cons x L ih =>
    intro hL
    have hx := hL x (by simp)
    have ih' := ih (fun v hv => hL v (by simp [hv]))
    by_cases h : x < t
    · have e : (x :: L).filter (fun v => decide (v < t))
          = x :: L.filter (fun v => decide (v < t)) :=
        List.filter_cons_of_pos (by simpa using h)
      rw [e]
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · have e : (x :: L).filter (fun v => decide (v < t))
          = L.filter (fun v => decide (v < t)) :=
        List.filter_cons_of_neg (by simpa using h)
      rw [e]
      simp only [List.map_cons, List.sum_cons]
      omega
theorem s_split_r (L : List ℕ) (t c r : ℕ) (htc : t ≤ c) (htr : t ≤ r) :
    r ∈ L →
    (L.map (fun v => t - v)).sum + (L.filter (fun v => decide (v < t))).length * (c - t) + (c - r)
      ≤ (L.map (fun v => c - v)).sum := by
  induction L with
  | nil => intro h; simp at h
  | cons x L ih =>
    intro hr
    rcases List.mem_cons.1 hr with hxr | hrL
    · have hx : ¬ x < t := by omega
      have e : (x :: L).filter (fun v => decide (v < t))
          = L.filter (fun v => decide (v < t)) :=
        List.filter_cons_of_neg (by simpa using hx)
      rw [e]
      simp only [List.map_cons, List.sum_cons]
      have h2 := s_split_le L t c htc
      omega
    · have ih' := ih hrL
      by_cases h : x < t
      · have e : (x :: L).filter (fun v => decide (v < t))
            = x :: L.filter (fun v => decide (v < t)) :=
          List.filter_cons_of_pos (by simpa using h)
        rw [e]
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · have e : (x :: L).filter (fun v => decide (v < t))
            = L.filter (fun v => decide (v < t)) :=
          List.filter_cons_of_neg (by simpa using h)
        rw [e]
        simp only [List.map_cons, List.sum_cons]
        omega
theorem h_step : ∀ (G R : List ℕ) (cap r : ℕ),
  (∀ t : ℕ, (R.map (fun v => t-v)).sum ≤ (G.map (fun v => t-v)).sum) → r ∈ R → r ≤ cap →
  ∃ u : ℕ, (G.filter (fun v => decide (v ≤ cap))).max? = some u ∧
    ∀ t : ℕ, (((r+1) :: R.erase r).map (fun v => t-v)).sum ≤ (((u+1) :: G.erase u).map (fun v => t-v)).sum := by
  intro G R cap r hdom hr hrc
  have hpos : 0 < (G.map (fun v => (cap + 1) - v)).sum := by
    have h1 := hdom (cap + 1)
    have h2 := s_erase R r (cap + 1) hr
    omega
  obtain ⟨w, hwG, hwc⟩ := s_pos G (cap + 1) hpos
  have hwF : w ∈ G.filter (fun v => decide (v ≤ cap)) :=
    List.mem_filter.2 ⟨hwG, by simpa using (show w ≤ cap by omega)⟩
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (List.isSome_max?_of_mem hwF)
  have hu2 : u ∈ G.filter (fun v => decide (v ≤ cap))
      ∧ ∀ b, b ∈ G.filter (fun v => decide (v ≤ cap)) → b ≤ u := by
    exact List.max?_eq_some_iff.1 hu
  have huG : u ∈ G := (List.mem_filter.1 hu2.1).1
  have hmax : ∀ v ∈ G, v ≤ cap → v ≤ u := fun v hv hvc =>
    hu2.2 v (List.mem_filter.2 ⟨hv, by simpa using hvc⟩)
  refine ⟨u, hu, ?_⟩
  intro t
  simp only [List.map_cons, List.sum_cons]
  have eR := s_erase R r t hr
  have eG := s_erase G u t huG
  have hdt := hdom t
  rcases Nat.lt_or_ge u t with hut | hut
  · rcases Nat.lt_or_ge r t with hrt | hrt
    · omega
    · have key : (R.map (fun v => t - v)).sum < (G.map (fun v => t - v)).sum := by
        obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        by_contra hcon
        have sR := s_slope R s
        have sG := s_slope G s
        have hds := hdom s
        have hk : (G.filter (fun v => decide (v < s + 1))).length
            ≤ (R.filter (fun v => decide (v < s + 1))).length := by
          omega
        have hGeq := s_split_eq G (s + 1) (cap + 1) (by omega) (fun v hv => by
          by_cases hvc : v ≤ cap
          · left
            have := hmax v hv hvc
            omega
          · right
            omega)
        have hRle := s_split_r R (s + 1) (cap + 1) r (by omega) hrt hr
        have hmul : (G.filter (fun v => decide (v < s + 1))).length * (cap + 1 - (s + 1))
            ≤ (R.filter (fun v => decide (v < s + 1))).length * (cap + 1 - (s + 1)) :=
          Nat.mul_le_mul hk (Nat.le_refl _)
        have hc := hdom (cap + 1)
        omega
      omega
  · omega
theorem h_upd : ∀ (p : ℕ) (f g : Fin p → ℕ) (l : Fin p),
  (∀ x : Fin p, g x = if x = l then f x + 1 else f x) →
  List.Perm ((List.finRange p).map g) ((f l + 1) :: ((List.finRange p).map f).erase (f l)) := by
  intro p f g l hg
  have hl : l ∈ List.finRange p := List.mem_finRange l
  have hp : List.Perm (List.finRange p) (l :: (List.finRange p).erase l) := List.perm_cons_erase hl
  have hnd : (List.finRange p).Nodup := List.nodup_finRange p
  have hmap : ((List.finRange p).erase l).map g = ((List.finRange p).erase l).map f := by
    apply List.map_congr_left
    intro a ha
    have hne : a ≠ l := ((List.Nodup.mem_erase_iff hnd).1 ha).1
    rw [hg a, ite_eq_right hne]
  have hgl : g l = f l + 1 := by
    rw [hg l, ite_eq_left rfl]
  have h1 : List.Perm ((List.finRange p).map g) ((f l + 1) :: ((List.finRange p).erase l).map f) := by
    have h3 := hp.map g
    rw [List.map_cons, hgl, hmap] at h3
    exact h3
  have h2 : List.Perm (((List.finRange p).map f).erase (f l)) (((List.finRange p).erase l).map f) := by
    have h4 := (hp.map f).erase (f l)
    rw [List.map_cons, List.erase_cons_head] at h4
    exact h4
  exact h1.trans (h2.cons _).symm
def d_cnt (n p : ℕ) (c : Fin n → Fin p) (k : ℕ) (label : Fin p) : ℕ :=
  (Finset.univ.filter (fun j : Fin n => j.val < k ∧ c j = label)).card
theorem d_take (n k : ℕ) (hk : k < n) :
    (List.finRange n).take (k+1) = (List.finRange n).take k ++ [⟨k, hk⟩] := by
  have h' : k < (List.finRange n).length := by simpa using hk
  rw [List.take_succ_eq_append_getElem h']
  simp
theorem d_cnt_succ (n p : ℕ) (c : Fin n → Fin p) (k : ℕ) (hk : k < n) (x : Fin p) :
    d_cnt n p c (k+1) x = if x = c ⟨k, hk⟩ then d_cnt n p c k x + 1 else d_cnt n p c k x := by
  unfold d_cnt
  split_ifs with h
  · subst h
    have e : (Finset.univ.filter (fun j : Fin n => j.val < k+1 ∧ c j = c ⟨k, hk⟩)) =
        insert ⟨k, hk⟩ (Finset.univ.filter (fun j : Fin n => j.val < k ∧ c j = c ⟨k, hk⟩)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        rcases (show j.val < k ∨ j.val = k by omega) with h3 | h3
        · exact Or.inr ⟨h3, h2⟩
        · exact Or.inl (Fin.ext h3)
      · rintro (h3 | ⟨h3, h4⟩)
        · subst h3
          exact ⟨Nat.lt_succ_self k, rfl⟩
        · exact ⟨Nat.lt_succ_of_lt h3, h4⟩
    rw [e, Finset.card_insert_of_notMem]
    simp
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rcases (show j.val < k ∨ j.val = k by omega) with h3 | h3
      · exact h3
      · exfalso
        apply h
        rw [← h2]
        exact congrArg c (Fin.ext h3)
    · rintro ⟨h1, h2⟩
      exact ⟨Nat.lt_succ_of_lt h1, h2⟩
theorem d_run (n p : ℕ) (b : Fin n → ℕ) (c : Fin n → Fin p)
    (hc : ∀ i : Fin n, (Finset.univ.filter (fun j : Fin n => j < i ∧ c j = c i)).card ≤ b i) :
    ∀ k : ℕ, k ≤ n → ∃ L : List ℕ, (((List.finRange n).take k).map b).foldl
      (fun (state : Option (List ℕ)) (cap : ℕ) =>
        state.bind (fun loads =>
          ((loads.filter (fun v => decide (v ≤ cap))).max?).map
            (fun v => (v+1) :: loads.erase v))) (some (List.replicate p 0)) = some L ∧ ∀ t : ℕ,
      ((List.finRange p).map (fun label => t - d_cnt n p c k label)).sum ≤
        (L.map (fun v => t-v)).sum := by
  intro k
  induction k with
  | zero =>
    intro _
    have e0 : ∀ x : Fin p, d_cnt n p c 0 x = 0 := by
      intro x
      unfold d_cnt
      simp
    refine ⟨List.replicate p 0, rfl, fun t => ?_⟩
    apply le_of_eq
    simp only [e0, Nat.sub_zero, List.map_replicate, List.map_const', List.length_finRange]
  | succ k ih =>
    intro hk1
    have hk : k < n := by omega
    obtain ⟨L, hL, hdom⟩ := ih (by omega)
    have hr : d_cnt n p c k (c ⟨k, hk⟩) ≤ b ⟨k, hk⟩ := by
      have e : d_cnt n p c k (c ⟨k, hk⟩) =
          (Finset.univ.filter (fun j : Fin n => j < ⟨k, hk⟩ ∧ c j = c ⟨k, hk⟩)).card := by
        unfold d_cnt
        exact congrArg Finset.card (Finset.filter_congr (fun j _ => Iff.rfl))
      rw [e]
      exact hc ⟨k, hk⟩
    have h1 : ∀ t : ℕ, (((List.finRange p).map (d_cnt n p c k)).map (fun v => t-v)).sum ≤
        (L.map (fun v => t-v)).sum := by
      intro t
      rw [List.map_map]
      exact hdom t
    obtain ⟨u, hu, hd⟩ := h_step L ((List.finRange p).map (d_cnt n p c k)) (b ⟨k, hk⟩)
      (d_cnt n p c k (c ⟨k, hk⟩)) h1 (List.mem_map.2 ⟨c ⟨k, hk⟩, List.mem_finRange _, rfl⟩) hr
    have hp := h_upd p (d_cnt n p c k) (d_cnt n p c (k+1)) (c ⟨k, hk⟩)
      (fun x => d_cnt_succ n p c k hk x)
    refine ⟨(u+1) :: L.erase u, ?_, ?_⟩
    · rw [d_take n k hk, List.map_append, List.foldl_append, hL]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, Option.bind_some,
        hu, Option.map_some]
    · intro t
      have e1 := (hp.map (fun v => t - v)).sum_eq
      rw [List.map_map] at e1
      exact le_trans (le_of_eq e1) (hd t)
theorem d_main (n p : ℕ) (b : Fin n → ℕ) (c : Fin n → Fin p)
    (hc : ∀ i : Fin n, (Finset.univ.filter (fun j : Fin n => j < i ∧ c j = c i)).card ≤ b i) :
    ∃ loads : List ℕ, ((List.finRange n).map b).foldl
      (fun (state : Option (List ℕ)) (cap : ℕ) =>
        state.bind (fun loads =>
          ((loads.filter (fun v => decide (v ≤ cap))).max?).map
            (fun v => (v+1) :: loads.erase v))) (some (List.replicate p 0)) = some loads ∧ ∀ t : ℕ,
      ((List.finRange p).map (fun label => t - (Finset.univ.filter (fun i : Fin n => c i = label)).card)).sum ≤
        (loads.map (fun v => t-v)).sum := by
  obtain ⟨L, hL, hdom⟩ := d_run n p b c hc n le_rfl
  have ht : (List.finRange n).take n = List.finRange n := List.take_of_length_le (by simp)
  rw [ht] at hL
  refine ⟨L, hL, fun t => ?_⟩
  have e : ∀ x : Fin p, d_cnt n p c n x = (Finset.univ.filter (fun i : Fin n => c i = x)).card := by
    intro x
    unfold d_cnt
    congr 1
    ext j
    simp
  simp only [e] at hdom
  exact hdom t
theorem h_dom : ∀ (n p : ℕ) (b : Fin n → ℕ),
  let step := fun (state : Option (List ℕ)) (cap : ℕ) =>
    state.bind (fun loads =>
      ((loads.filter (fun v => decide (v ≤ cap))).max?).map
        (fun v => (v+1) :: loads.erase v))
  let result := ((List.finRange n).map b).foldl step (some (List.replicate p 0))
  let fits := fun c : Fin n → Fin p => ∀ i : Fin n,
    (Finset.univ.filter (fun j : Fin n => j < i ∧ c j = c i)).card ≤ b i
  ∀ c : Fin n → Fin p, fits c → ∃ loads : List ℕ, result = some loads ∧ ∀ t : ℕ,
    ((List.finRange p).map (fun label => t - (Finset.univ.filter (fun i : Fin n => c i = label)).card)).sum ≤
      (loads.map (fun v => t-v)).sum := by
  intro n p b step result fits c hc
  exact d_main n p b c hc
def b_step (state : Option (List ℕ)) (cap : ℕ) : Option (List ℕ) :=
  state.bind (fun loads =>
    ((loads.filter (fun v => decide (v ≤ cap))).max?).map
      (fun v => (v+1) :: loads.erase v))
theorem b_none (l : List ℕ) : l.foldl b_step none = none := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons]
    exact ih
theorem b_nil (l : List ℕ) (h : l ≠ []) : l.foldl b_step (some []) = none := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs =>
    rw [List.foldl_cons]
    exact b_none xs
theorem b_step_some (s : Option (List ℕ)) (cap : ℕ) (L' : List ℕ) (h : b_step s cap = some L') :
    ∃ L v, s = some L ∧ (L.filter (fun x => decide (x ≤ cap))).max? = some v ∧
      L' = (v + 1) :: L.erase v := by
  cases s with
  | none => simp [b_step] at h
  | some L =>
    have e : b_step (some L) cap = ((L.filter (fun x => decide (x ≤ cap))).max?).map
        (fun v => (v + 1) :: L.erase v) := rfl
    rw [e] at h
    cases hm : (L.filter (fun x => decide (x ≤ cap))).max? with
    | none =>
      rw [hm] at h
      simp at h
    | some v =>
      rw [hm] at h
      exact ⟨L, v, rfl, hm, (Option.some.inj h).symm⟩
theorem b_take (n k : ℕ) (hk : k < n) :
    (List.finRange n).take (k + 1) = (List.finRange n).take k ++ [⟨k, hk⟩] := by
  have hlen : k < (List.finRange n).length := by simpa using hk
  rw [List.take_add_one, List.getElem?_eq_getElem hlen]
  simp
theorem b_perm (p : ℕ) (f g : Fin p → ℕ) (l : Fin p) (L : List ℕ) (v : ℕ)
    (hg : ∀ x : Fin p, g x = if x = l then f x + 1 else f x)
    (hL : List.Perm L ((List.finRange p).map f)) (hv : f l = v) :
    List.Perm ((v + 1) :: L.erase v) ((List.finRange p).map g) := by
  subst hv
  exact ((hL.erase (f l)).cons (f l + 1)).trans (h_upd p f g l hg).symm
theorem b_cnt (n p k : ℕ) (hk : k < n) (c : Fin n → Fin p) (l x : Fin p) :
    (Finset.univ.filter (fun j : Fin n => j.val < k + 1 ∧ (if j.val = k then l else c j) = x)).card =
      if x = l then (Finset.univ.filter (fun j : Fin n => j.val < k ∧ c j = x)).card + 1
      else (Finset.univ.filter (fun j : Fin n => j.val < k ∧ c j = x)).card := by
  by_cases hx : x = l
  · rw [ite_eq_left hx, hx]
    have hnot : (⟨k, hk⟩ : Fin n) ∉ Finset.univ.filter (fun j : Fin n => j.val < k ∧ c j = l) := by
      simp
    rw [← Finset.card_insert_of_notMem hnot]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hj : j.val = k
    · rw [ite_eq_left hj]
      exact ⟨fun _ => Or.inl (Fin.ext hj), fun _ => ⟨by omega, rfl⟩⟩
    · rw [ite_eq_right hj]
      constructor
      · rintro ⟨h1, h2⟩
        exact Or.inr ⟨by omega, h2⟩
      · rintro (h | ⟨h1, h2⟩)
        · exact absurd (congrArg Fin.val h) hj
        · exact ⟨by omega, h2⟩
  · rw [ite_eq_right hx]
    congr 1
    apply Finset.filter_congr
    intro j _
    by_cases hj : j.val = k
    · rw [ite_eq_left hj]
      constructor
      · rintro ⟨_, h2⟩
        exact absurd h2.symm hx
      · rintro ⟨h1, _⟩
        exact absurd hj (by omega)
    · rw [ite_eq_right hj]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
theorem b_fit (n p k : ℕ) (hk : k < n) (b : Fin n → ℕ) (c : Fin n → Fin p) (l : Fin p)
    (hc : ∀ i : Fin n, i.val < k →
      (Finset.univ.filter (fun j : Fin n => j < i ∧ c j = c i)).card ≤ b i)
    (hl : (Finset.univ.filter (fun j : Fin n => j.val < k ∧ c j = l)).card ≤ b ⟨k, hk⟩) :
    ∀ i : Fin n, i.val < k + 1 → (Finset.univ.filter (fun j : Fin n =>
      j < i ∧ (if j.val = k then l else c j) = (if i.val = k then l else c i))).card ≤ b i := by
  intro i hi
  by_cases hik : i.val = k
  · have e : Finset.univ.filter (fun j : Fin n =>
        j < i ∧ (if j.val = k then l else c j) = (if i.val = k then l else c i)) =
        Finset.univ.filter (fun j : Fin n => j.val < k ∧ c j = l) := by
      apply Finset.filter_congr
      intro j _
      rw [ite_eq_left hik]
      constructor
      · rintro ⟨h1, h2⟩
        have h3 : j.val < i.val := Fin.lt_def.mp h1
        have hjk : ¬ j.val = k := by omega
        rw [ite_eq_right hjk] at h2
        exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        have hjk : ¬ j.val = k := by omega
        rw [ite_eq_right hjk]
        exact ⟨Fin.lt_def.mpr (by omega), h2⟩
    have hi' : i = ⟨k, hk⟩ := Fin.ext hik
    rw [e, hi']
    exact hl
  · have e : Finset.univ.filter (fun j : Fin n =>
        j < i ∧ (if j.val = k then l else c j) = (if i.val = k then l else c i)) =
        Finset.univ.filter (fun j : Fin n => j < i ∧ c j = c i) := by
      apply Finset.filter_congr
      intro j _
      rw [ite_eq_right hik]
      constructor
      · rintro ⟨h1, h2⟩
        have h3 : j.val < i.val := Fin.lt_def.mp h1
        have hjk : ¬ j.val = k := by omega
        rw [ite_eq_right hjk] at h2
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        have h3 : j.val < i.val := Fin.lt_def.mp h1
        have hjk : ¬ j.val = k := by omega
        rw [ite_eq_right hjk]
        exact ⟨h1, h2⟩
    rw [e]
    exact hc i (by omega)
theorem b_inv (n p : ℕ) (b : Fin n → ℕ) (hp : 0 < p) : ∀ k, k ≤ n → ∀ L : List ℕ,
    (((List.finRange n).take k).map b).foldl b_step (some (List.replicate p 0)) = some L →
    ∃ c : Fin n → Fin p,
      (∀ i : Fin n, i.val < k →
        (Finset.univ.filter (fun j : Fin n => j < i ∧ c j = c i)).card ≤ b i) ∧
      List.Perm L ((List.finRange p).map
        (fun x => (Finset.univ.filter (fun j : Fin n => j.val < k ∧ c j = x)).card)) := by
  intro k
  induction k with
  | zero =>
    intro _ L hL
    simp only [List.take_zero, List.map_nil, List.foldl_nil, Option.some.injEq] at hL
    subst hL
    refine ⟨fun _ => ⟨0, hp⟩, fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
    apply List.Perm.of_eq
    simp [List.map_const']
  | succ k ih =>
    intro hk L' hL'
    have hk' : k < n := hk
    rw [b_take n k hk', List.map_append, List.foldl_append] at hL'
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at hL'
    obtain ⟨L, v, hrun, hv, rfl⟩ := b_step_some _ _ _ hL'
    obtain ⟨c, hc1, hc2⟩ := ih (Nat.le_of_lt hk') L hrun
    have hvmem := List.max?_mem hv
    rw [List.mem_filter] at hvmem
    obtain ⟨hvL, hvb⟩ := hvmem
    have hvb' : v ≤ b ⟨k, hk'⟩ := of_decide_eq_true hvb
    obtain ⟨l, -, hl⟩ := List.mem_map.mp (hc2.subset hvL)
    refine ⟨fun j => if j.val = k then l else c j, ?_, ?_⟩
    · exact b_fit n p k hk' b c l hc1 ((le_of_eq hl).trans hvb')
    · exact b_perm p (fun x => (Finset.univ.filter (fun j : Fin n => j.val < k ∧ c j = x)).card)
        (fun x => (Finset.univ.filter (fun j : Fin n =>
          j.val < k + 1 ∧ (if j.val = k then l else c j) = x)).card) l L v
        (b_cnt n p k hk' c l) hc2 hl
theorem b_main (n p : ℕ) (b : Fin n → ℕ)
    (h : (((List.finRange n).map b).foldl b_step (some (List.replicate p 0))).isSome = true) :
    ∃ c : Fin n → Fin p, ∀ i : Fin n,
      (Finset.univ.filter (fun j : Fin n => j < i ∧ c j = c i)).card ≤ b i := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact ⟨fun i => i.elim0, fun i => i.elim0⟩
    · have h1 : ((List.finRange n).map b) ≠ [] := List.ne_nil_of_length_pos (by simpa using hn)
      have h2 : ((List.finRange n).map b).foldl b_step (some (List.replicate 0 0)) = none :=
        b_nil _ h1
      rw [h2] at h
      simp at h
  · obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp h
    have e : (List.finRange n).take n = List.finRange n := List.take_of_length_le (by simp)
    obtain ⟨c, hc, -⟩ := b_inv n p b hp n le_rfl L (by rw [e]; exact hL)
    exact ⟨c, fun i => hc i i.isLt⟩
theorem h_build : ∀ (n p : ℕ) (b : Fin n → ℕ),
  let step := fun (state : Option (List ℕ)) (cap : ℕ) =>
    state.bind (fun loads =>
      ((loads.filter (fun v => decide (v ≤ cap))).max?).map
        (fun v => (v+1) :: loads.erase v))
  let result := ((List.finRange n).map b).foldl step (some (List.replicate p 0))
  let fits := fun c : Fin n → Fin p => ∀ i : Fin n,
    (Finset.univ.filter (fun j : Fin n => j < i ∧ c j = c i)).card ≤ b i
  (result.isSome = true → ∃ c : Fin n → Fin p, fits c) := by
  intro n p b step result fits h
  exact b_main n p b h
theorem h_glue : ∀ (n p : ℕ) (b : Fin n → ℕ),
  let step := fun (state : Option (List ℕ)) (cap : ℕ) =>
    state.bind (fun loads =>
      ((loads.filter (fun v => decide (v ≤ cap))).max?).map
        (fun v => (v+1) :: loads.erase v))
  let result := ((List.finRange n).map b).foldl step (some (List.replicate p 0))
  let fits := fun c : Fin n → Fin p => ∀ i : Fin n,
    (Finset.univ.filter (fun j : Fin n => j < i ∧ c j = c i)).card ≤ b i
  (result.isSome = true ↔ ∃ c : Fin n → Fin p, fits c) ∧
  ∀ loads : List ℕ, result = some loads → ∀ c : Fin n → Fin p, fits c → ∀ t : ℕ,
    ((List.finRange p).map (fun label => t - (Finset.univ.filter (fun i : Fin n => c i = label)).card)).sum ≤
      (loads.map (fun v => t-v)).sum := by
  intro n p b step result fits
  have hD : ∀ c : Fin n → Fin p, fits c → ∃ loads : List ℕ, result = some loads ∧ ∀ t : ℕ,
    ((List.finRange p).map (fun label => t - (Finset.univ.filter (fun i : Fin n => c i = label)).card)).sum ≤
      (loads.map (fun v => t-v)).sum := h_dom n p b
  have hB : result.isSome = true → ∃ c : Fin n → Fin p, fits c := h_build n p b
  refine ⟨⟨hB, ?_⟩, ?_⟩
  · rintro ⟨c, hc⟩
    obtain ⟨loads, hres, -⟩ := hD c hc
    exact Option.isSome_iff_exists.2 ⟨loads, hres⟩
  · intro loads hres c hc t
    obtain ⟨loads', hres', hsum⟩ := hD c hc
    have heq : loads' = loads := Option.some.inj (hres'.symm.trans hres)
    subst heq
    exact hsum t
end PEqualNP.Outside.L_lib_909
theorem PEqualNP.Outside.L_lib_909 : ∀ (n p : ℕ) (b : Fin n → ℕ),
  let step := fun (state : Option (List ℕ)) (cap : ℕ) =>
    state.bind (fun loads =>
      ((loads.filter (fun v => decide (v ≤ cap))).max?).map
        (fun v => (v+1) :: loads.erase v))
  let result := ((List.finRange n).map b).foldl step (some (List.replicate p 0))
  let fits := fun c : Fin n → Fin p => ∀ i : Fin n,
    (Finset.univ.filter (fun j : Fin n => j < i ∧ c j = c i)).card ≤ b i
  (result.isSome = true ↔ ∃ c : Fin n → Fin p, fits c) ∧
  ∀ loads : List ℕ, result = some loads → ∀ c : Fin n → Fin p, fits c → ∀ t : ℕ,
    ((List.finRange p).map (fun label => t - (Finset.univ.filter (fun i : Fin n => c i = label)).card)).sum ≤
      (loads.map (fun v => t-v)).sum :=
  PEqualNP.Outside.L_lib_909.h_glue
