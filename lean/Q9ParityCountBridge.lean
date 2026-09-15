import Q9CNFSemantics

/-! Small cardinality lemmas used when replacing the competitive search by the
    r=4/r=5 LRAT certificate.  They relate the sequential-counter prefix
    counts to the parity count of a nine-point embedding. -/

namespace Erdos811Q9ParityCountBridge

open Mathlib.Tactic.Sat
open Erdos811
open Erdos811Q9SeqCounter
open Erdos811Q9CNFSemantics

lemma odd_prefixCount_le_parity_sum
    {ys : List Nat} {g : Fin 9 ↪ Fin 73}
    (hcoverage : ∀ z, z ∈ ys → ∃ i : Fin 9, z = (g i).val) :
    prefixCount (q9OddSelectionBool ys) 36 ≤
      ∑ i : Fin 9, (g i).val % 2 := by
  let J : Finset Nat :=
    (Finset.range 36).filter (fun j => q9OddSelectionBool ys j = true)
  let O : Finset (Fin 9) :=
    Finset.univ.filter (fun i => (g i).val % 2 = 1)
  have hprefix : prefixCount (q9OddSelectionBool ys) 36 = J.card := by
    simpa [J, prefixCount] using
      (Finset.sum_boole (p := fun j : Nat =>
        q9OddSelectionBool ys j = true) (s := Finset.range 36))
  have hodd (j : Nat) (hj : j ∈ J) : (2 * j + 1) % 2 = 1 := by
    have hj' : j < 36 := by
      exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    omega
  have hvalue (j : Nat) (hj : j ∈ J) : 2 * j + 1 ∈ ys := by
    have hsel : q9OddSelectionBool ys j = true :=
      (Finset.mem_filter.mp hj).2
    exact (selectionBool_true_iff ys (2 * j + 1)).mp (by
      simpa [q9OddSelectionBool] using hsel)
  have himage :
      (J.image (fun j => 2 * j + 1)) ⊆
        (O.image (fun i : Fin 9 => (g i).val)) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
    obtain ⟨i, hi⟩ := hcoverage (2 * j + 1) (hvalue j hj)
    have hiO : i ∈ O := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by rw [← hi]; exact hodd j hj⟩
    exact Finset.mem_image.mpr ⟨i, hiO, hi.symm⟩
  have hJinj : Set.InjOn (fun j : Nat => 2 * j + 1) (J : Set Nat) := by
    intro a ha b hb hab
    change 2 * a + 1 = 2 * b + 1 at hab
    omega
  have hcardJ : (J.image (fun j => 2 * j + 1)).card = J.card :=
    Finset.card_image_of_injOn hJinj
  have hGi : Set.InjOn (fun i : Fin 9 => (g i).val) (O : Set (Fin 9)) := by
    intro a ha b hb hab
    exact g.injective (Fin.ext hab)
  have hcardO : (O.image (fun i : Fin 9 => (g i).val)).card = O.card :=
    Finset.card_image_of_injOn hGi
  have hcard_le : J.card ≤ O.card := by
    rw [← hcardJ, ← hcardO]
    exact Finset.card_le_card himage
  rw [hprefix]
  exact hcard_le.trans_eq (by
    calc
      O.card = ∑ i : Fin 9, if (g i).val % 2 = 1 then 1 else 0 := by
        simpa [O] using
          (Finset.sum_boole (p := fun i : Fin 9 =>
            (g i).val % 2 = 1) (s := (Finset.univ : Finset (Fin 9))))
      _ = ∑ i : Fin 9, (g i).val % 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases h : (g i).val % 2 = 1 <;> simp [h] <;> omega)

lemma odd_prefixCount_eq_parity_sum
    {ys : List Nat} {g : Fin 9 ↪ Fin 73}
    (hcoverage : ∀ z, z ∈ ys → ∃ i : Fin 9, z = (g i).val)
    (himage : ∀ i : Fin 9, (g i).val ∈ ys) :
    prefixCount (q9OddSelectionBool ys) 36 =
      ∑ i : Fin 9, (g i).val % 2 := by
  let J : Finset Nat :=
    (Finset.range 36).filter (fun j => q9OddSelectionBool ys j = true)
  let O : Finset (Fin 9) :=
    Finset.univ.filter (fun i => (g i).val % 2 = 1)
  have hprefix : prefixCount (q9OddSelectionBool ys) 36 = J.card := by
    simpa [J, prefixCount] using
      (Finset.sum_boole (p := fun j : Nat =>
        q9OddSelectionBool ys j = true) (s := Finset.range 36))
  have hodd (j : Nat) (hj : j ∈ J) : (2 * j + 1) % 2 = 1 := by
    have hj' : j < 36 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    omega
  have hvalue (j : Nat) (hj : j ∈ J) : 2 * j + 1 ∈ ys := by
    have hsel : q9OddSelectionBool ys j = true :=
      (Finset.mem_filter.mp hj).2
    exact (selectionBool_true_iff ys (2 * j + 1)).mp (by
      simpa [q9OddSelectionBool] using hsel)
  have hJtoO :
      (J.image (fun j => 2 * j + 1)) ⊆
        (O.image (fun i : Fin 9 => (g i).val)) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
    obtain ⟨i, hi⟩ := hcoverage (2 * j + 1) (hvalue j hj)
    have hiO : i ∈ O := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by rw [← hi]; exact hodd j hj⟩
    exact Finset.mem_image.mpr ⟨i, hiO, hi.symm⟩
  have hOtoJ :
      (O.image (fun i : Fin 9 => (g i).val)) ⊆
        (J.image (fun j => 2 * j + 1)) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    let j : Nat := (g i).val / 2
    have hiodd : (g i).val % 2 = 1 := (Finset.mem_filter.mp hi).2
    have hjlt : j < 36 := by
      dsimp [j]
      have hlt : (g i).val < 73 := (g i).isLt
      omega
    have hjvalue : 2 * j + 1 = (g i).val := by
      dsimp [j]
      omega
    have hj : j ∈ J := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hjlt, ?_⟩
      apply (selectionBool_true_iff ys (2 * j + 1)).2
      rw [hjvalue]
      exact himage i
    exact Finset.mem_image.mpr ⟨j, hj, hjvalue⟩
  have hJinj : Set.InjOn (fun j : Nat => 2 * j + 1) (J : Set Nat) := by
    intro a ha b hb hab
    change 2 * a + 1 = 2 * b + 1 at hab
    omega
  have hcardJ : (J.image (fun j => 2 * j + 1)).card = J.card :=
    Finset.card_image_of_injOn hJinj
  have hGi : Set.InjOn (fun i : Fin 9 => (g i).val) (O : Set (Fin 9)) := by
    intro a ha b hb hab
    exact g.injective (Fin.ext hab)
  have hcardO : (O.image (fun i : Fin 9 => (g i).val)).card = O.card :=
    Finset.card_image_of_injOn hGi
  have hcard : J.card = O.card := by
    apply Nat.le_antisymm
    · rw [← hcardJ, ← hcardO]
      exact Finset.card_le_card hJtoO
    · rw [← hcardO, ← hcardJ]
      exact Finset.card_le_card hOtoJ
  rw [hprefix, hcard]
  calc
    O.card = ∑ i : Fin 9, if (g i).val % 2 = 1 then 1 else 0 := by
      simpa [O] using
        (Finset.sum_boole (p := fun i : Fin 9 =>
          (g i).val % 2 = 1) (s := (Finset.univ : Finset (Fin 9))))
    _ = ∑ i : Fin 9, (g i).val % 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : (g i).val % 2 = 1 <;> simp [h] <;> omega

lemma base_prefixCount_le_of_card
    {ys : List Nat}
    (hbound : ∀ z, z ∈ ys → z < 73)
    (hcard : 9 ≤ ys.toFinset.card) :
    prefixCount (fun i => !(selectionBool ys i)) 73 ≤ 64 := by
  let N : Finset Nat :=
    (Finset.range 73).filter (fun i => !(selectionBool ys i) = true)
  have hprefix :
      prefixCount (fun i => !(selectionBool ys i)) 73 = N.card := by
    simpa [N, prefixCount] using
      (Finset.sum_boole (p := fun i : Nat =>
        !(selectionBool ys i) = true) (s := Finset.range 73))
  have hsub : ys.toFinset ⊆ Finset.range 73 := by
    intro z hz
    exact Finset.mem_range.mpr (hbound z (List.mem_toFinset.mp hz))
  have hN : N = (Finset.range 73 \ ys.toFinset) := by
    ext i
    simp [N, selectionBool]
  have hinter : ys.toFinset ∩ Finset.range 73 = ys.toFinset :=
    Finset.inter_eq_left.mpr hsub
  rw [hprefix, hN, Finset.card_sdiff, hinter, Finset.card_range]
  omega

end Erdos811Q9ParityCountBridge
