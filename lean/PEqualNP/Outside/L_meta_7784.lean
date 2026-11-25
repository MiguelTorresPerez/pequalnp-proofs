import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7784

abbrev F := (Fin 26 → Bool) → Bool

def S (f : F) : Bool → Set (Fin 26 → Bool) := fun b => {x | f x = b}

def dz : F := fun _ => false

def gate (L : List F) (i j : ℕ) (o : Bool) : F :=
  fun x => if o then (L.getD i dz x || L.getD j dz x) else (L.getD i dz x && L.getD j dz x)

def build (L : List F) : List (ℕ × ℕ × Bool) → List F
  | [] => []
  | (i, j, o) :: ds => gate L i j o :: build (L ++ [gate L i j o]) ds

def valid (n : ℕ) : List (ℕ × ℕ × Bool) → Bool
  | [] => true
  | (i, j, _) :: ds => decide (i < n) && decide (j < n) && valid (n + 1) ds

theorem gate_sub (f h : F) (o b : Bool) :
    S (fun x => if o then (f x || h x) else (f x && h x)) b ⊆
      if b = o then S f b ∪ S h b else S f b ∩ S h b := by
  intro x hx
  have hx' : (if o then (f x || h x) else (f x && h x)) = b := hx
  clear hx
  cases o <;> cases b <;> cases hf : f x <;> cases hh : h x <;> simp_all [S]

theorem main : ∀ (ds : List (ℕ × ℕ × Bool)) (L : List F), valid L.length ds = true →
    ∀ (k : ℕ) (hk : k < ((build L ds).map S).length),
      ∃ x7 ∈ L.map S ++ List.take k ((build L ds).map S),
      ∃ x8 ∈ L.map S ++ List.take k ((build L ds).map S), ∃ (x9 : Bool), ∀ (x10 : Bool),
        ((build L ds).map S)[k] x10 ⊆ if x10 = x9 then x7 x10 ∪ x8 x10 else x7 x10 ∩ x8 x10 := by
  intro ds
  induction ds with
  | nil => intro L _ k hk; simp [build] at hk
  | cons d ds ih =>
    obtain ⟨i, j, o⟩ := d
    intro L hv k hk
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hi, hj⟩, hv⟩ := hv
    cases k with
    | zero =>
      refine ⟨S (L.getD i dz), ?_, S (L.getD j dz), ?_, o, ?_⟩
      · apply List.mem_append_left
        apply List.mem_map_of_mem
        rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
      · apply List.mem_append_left
        apply List.mem_map_of_mem
        rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
      · intro b
        exact gate_sub _ _ o b
    | succ k =>
      have hk' : k < ((build (L ++ [gate L i j o]) ds).map S).length := by
        simpa [build] using hk
      have hv' : valid (L ++ [gate L i j o]).length ds = true := by simpa using hv
      obtain ⟨x7, h7, x8, h8, x9, h⟩ := ih (L ++ [gate L i j o]) hv' k hk'
      refine ⟨x7, ?_, x8, ?_, x9, ?_⟩
      · simpa [build, List.take_succ_cons] using h7
      · simpa [build, List.take_succ_cons] using h8
      · intro b
        exact h b

def W : List F :=
  (List.ofFn fun (x1 : Fin (26 : ℕ)) (x2 : Fin (26 : ℕ) → Bool) => x2 x1) ++ [fun (x1 : Fin (26 : ℕ) → Bool) => x1 (0 : Fin (26 : ℕ)) || x1 (1 : Fin (26 : ℕ))]

def ds : List (ℕ × ℕ × Bool) :=
  [(26, 3, true), (27, 9, true), (28, 13, false),
   (12, 0, true), (30, 2, true), (31, 8, true), (32, 14, false),
   (10, 11, true), (34, 0, true), (35, 6, true), (36, 16, false),
   (4, 5, true), (38, 7, true), (39, 0, true), (40, 22, false),
   (29, 33, true), (42, 37, true), (43, 41, true)]

def A (x : Fin 26 → Bool) (i : Fin 13) : Bool := x (Fin.castAdd 13 i)
def B (x : Fin 26 → Bool) (i : Fin 13) : Bool := x (Fin.natAdd 13 i)

def out : F := fun x =>
  (((((A x 0 || A x 1) || A x 3) || A x 9) && B x 0) ||
   ((((A x 12 || A x 0) || A x 2) || A x 8) && B x 1) ||
   ((((A x 10 || A x 11) || A x 0) || A x 6) && B x 3)) ||
   ((((A x 4 || A x 5) || A x 7) || A x 0) && B x 9)

theorem hlen : (build W ds).length = 18 := by rfl

theorem hW : W.length = 27 := by simp [W]

theorem hout : out ∈ build W ds := by
  have h : (build W ds)[17]'(by rw [hlen]; decide) = out := by rfl
  rw [← h]; exact List.getElem_mem _

theorem hvalid : valid W.length ds = true := by
  rw [hW]; decide

theorem pairs : ∀ (x3 x4 : Fin 13), x4.val ∈ [0, 1, 3, 9] → (x3.val + x4.val) % 13 ∈ [0, 1, 3, 9] →
    (x4 = 0 ∧ (x3 = 0 ∨ x3 = 1 ∨ x3 = 3 ∨ x3 = 9)) ∨ (x4 = 1 ∧ (x3 = 12 ∨ x3 = 0 ∨ x3 = 2 ∨ x3 = 8)) ∨
    (x4 = 3 ∧ (x3 = 10 ∨ x3 = 11 ∨ x3 = 0 ∨ x3 = 6)) ∨ (x4 = 9 ∧ (x3 = 4 ∨ x3 = 5 ∨ x3 = 7 ∨ x3 = 0)) := by
  decide

theorem sem (x : Fin 26 → Bool) : out x = true ↔
    ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (x4 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ((x3 : ℕ) + (x4 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) x4) = Bool.true := by
  constructor
  · intro h
    simp only [out, A, B, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ((⟨(((h | h) | h) | h), hb⟩ | ⟨(((h | h) | h) | h), hb⟩) | ⟨(((h | h) | h) | h), hb⟩) | ⟨(((h | h) | h) | h), hb⟩ <;>
      exact ⟨_, _, by decide, by decide, h, hb⟩
  · rintro ⟨x3, x4, h1, h2, ha, hb⟩
    rcases pairs x3 x4 h1 h2 with ⟨rfl, (rfl | rfl | rfl | rfl)⟩ | ⟨rfl, (rfl | rfl | rfl | rfl)⟩ | ⟨rfl, (rfl | rfl | rfl | rfl)⟩ | ⟨rfl, (rfl | rfl | rfl | rfl)⟩ <;>
      (simp only [out, A, B, ha, hb]; simp)

end PEqualNP.Outside.L_meta_7784

theorem PEqualNP.Outside.L_meta_7784 : have x1 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := List.map (fun (x1 : (Fin (26 : ℕ) → Bool) → Bool) (x2 : Bool) => {x3 : Fin (26 : ℕ) → Bool | x1 x3 = x2}) ((List.ofFn fun (x1 : Fin (26 : ℕ)) (x2 : Fin (26 : ℕ) → Bool) => x2 x1) ++ [fun (x1 : Fin (26 : ℕ) → Bool) => x1 (0 : Fin (26 : ℕ)) || x1 (1 : Fin (26 : ℕ))]); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), ↑x4 ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∃ (x3 : List (Bool → Set (Fin (26 : ℕ) → Bool))) (x4 : Bool → Set (Fin (26 : ℕ) → Bool)),   x3.length ≤ (18 : ℕ) ∧     x4 ∈ x1 ++ x3 ∧       (∀ (x5 : Fin x3.length),           have x6 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := x1 ++ List.take (↑x5) x3;           ∃ x7 ∈ x6, ∃ x8 ∈ x6, ∃ (x9 : Bool), ∀ (x10 : Bool), x3.get x5 x10 ⊆ if x10 = x9 then x7 x10 ∪ x8 x10 else x7 x10 ∩ x8 x10) ∧         ∀ (x5 : Fin (26 : ℕ) → Bool), (x2 x5 → x5 ∈ x4 Bool.true) ∧ (¬x2 x5 → x5 ∈ x4 Bool.false) := by
  intro x1 x2
  refine ⟨(PEqualNP.Outside.L_meta_7784.build PEqualNP.Outside.L_meta_7784.W PEqualNP.Outside.L_meta_7784.ds).map PEqualNP.Outside.L_meta_7784.S, PEqualNP.Outside.L_meta_7784.S PEqualNP.Outside.L_meta_7784.out, ?_, ?_, ?_, ?_⟩
  · rw [List.length_map, PEqualNP.Outside.L_meta_7784.hlen]
  · apply List.mem_append_right
    exact List.mem_map_of_mem PEqualNP.Outside.L_meta_7784.hout
  · intro x5
    exact PEqualNP.Outside.L_meta_7784.main _ _ PEqualNP.Outside.L_meta_7784.hvalid x5.val x5.isLt
  · intro x5
    have h := PEqualNP.Outside.L_meta_7784.sem x5
    constructor
    · intro hx
      exact h.mpr hx
    · intro hx
      show PEqualNP.Outside.L_meta_7784.out x5 = false
      cases ho : PEqualNP.Outside.L_meta_7784.out x5
      · rfl
      · exact absurd (h.mp ho) hx
