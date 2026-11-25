import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6424

def ok (a b : Fin 13) : Bool :=
  let r := (a.val + b.val) % 13
  r != 0 && r != 1 && r != 3 && r != 9

def chk (a b c d : Fin 13) : Bool :=
  a == b || a == c || a == d || b == c || b == d || c == d ||
  decide (((List.finRange 13).filter
    (fun x => ok a x && ok b x && ok c x && ok d x)).length ≤ 3)

set_option maxRecDepth 100000 in
theorem key : (List.finRange 13).all (fun a => (List.finRange 13).all (fun b =>
    (List.finRange 13).all (fun c => (List.finRange 13).all (fun d => chk a b c d)))) = true := by
  decide +kernel

theorem key2 (a b c d : Fin 13) : chk a b c d = true := by
  have h := key
  simp only [List.all_eq_true, List.mem_finRange, forall_const] at h
  exact h a b c d

end PEqualNP.Outside.L_meta_6424

theorem PEqualNP.Outside.L_meta_6424 : ∀ (x1 x2 : Finset (Fin (13 : ℕ))), (∀ x3 ∈ x1, ∀ x5 ∈ x2, (↑x3 + ↑x5) % (13 : ℕ) ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → x1.card ≤ (3 : ℕ) ∨ x2.card ≤ (3 : ℕ) := by
  intro A B h
  by_contra hc
  rw [not_or, not_le, not_le] at hc
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < (A.erase a).card by
    rw [Finset.card_erase_of_mem ha]; omega)
  have hb1 := Finset.mem_erase.mp hb
  obtain ⟨c, hc1⟩ := Finset.card_pos.mp (show 0 < ((A.erase a).erase b).card by
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]; omega)
  have hc2 := Finset.mem_erase.mp hc1
  have hc3 := Finset.mem_erase.mp hc2.2
  obtain ⟨d, hd1⟩ := Finset.card_pos.mp (show 0 < (((A.erase a).erase b).erase c).card by
    rw [Finset.card_erase_of_mem hc1, Finset.card_erase_of_mem hb,
      Finset.card_erase_of_mem ha]; omega)
  have hd2 := Finset.mem_erase.mp hd1
  have hd3 := Finset.mem_erase.mp hd2.2
  have hd4 := Finset.mem_erase.mp hd3.2
  have hok : ∀ y ∈ A, ∀ x ∈ B, PEqualNP.Outside.L_meta_6424.ok y x = true := by
    intro y hy x hx
    have := h y hy x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    simp [PEqualNP.Outside.L_meta_6424.ok, this]
  have hk := PEqualNP.Outside.L_meta_6424.key2 a b c d
  have e1 : (a == b) = false := by simpa using Ne.symm hb1.1
  have e2 : (a == c) = false := by simpa using Ne.symm hc3.1
  have e3 : (a == d) = false := by simpa using Ne.symm hd4.1
  have e4 : (b == c) = false := by simpa using Ne.symm hc2.1
  have e5 : (b == d) = false := by simpa using Ne.symm hd3.1
  have e6 : (c == d) = false := by simpa using Ne.symm hd2.1
  simp only [PEqualNP.Outside.L_meta_6424.chk, e1, e2, e3, e4, e5, e6, Bool.false_or,
    decide_eq_true_eq] at hk
  have hsub : B ⊆ ((List.finRange 13).filter
    (fun x => PEqualNP.Outside.L_meta_6424.ok a x && PEqualNP.Outside.L_meta_6424.ok b x
      && PEqualNP.Outside.L_meta_6424.ok c x && PEqualNP.Outside.L_meta_6424.ok d x)).toFinset := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
      Bool.and_eq_true]
    exact ⟨⟨⟨hok a ha x hx, hok b hb1.2 x hx⟩, hok c hc3.2 x hx⟩, hok d hd4.2 x hx⟩
  have h1 := Finset.card_le_card hsub
  have h2 := List.toFinset_card_le ((List.finRange 13).filter
    (fun x => PEqualNP.Outside.L_meta_6424.ok a x && PEqualNP.Outside.L_meta_6424.ok b x
      && PEqualNP.Outside.L_meta_6424.ok c x && PEqualNP.Outside.L_meta_6424.ok d x))
  omega
