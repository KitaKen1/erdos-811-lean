import Q8PaperResidueSearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.BigOperators

namespace Erdos811

/-! The arbitrary infinity branch, before support normalization.

The seven finite vertices are represented by `x`; the eighth vertex is 56.
The residue edge list is ordered by vertex blocks, while the paper colour list
is ordered by pairs.  The bridge below is therefore a `List.Perm`, which is
exactly what is needed for colour-count arguments.
-/

def q8WithInfinity (x : Fin 7 → Nat) : Fin 8 → Nat :=
  Fin.lastCases 56 x

lemma q8WithInfinity_eq (x : Fin 7 → Nat) :
    q8WithInfinity x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, 56] := by
  funext i
  fin_cases i <;> rfl

def q8ResidueList (x : Fin 7 → Nat) : List Nat :=
  (List.ofFn x).map (fun v => v % 14)

lemma q8ResidueList_length (x : Fin 7 → Nat) :
    (q8ResidueList x).length = 7 := by
  simp [q8ResidueList]

lemma q8ResidueEdgeColors_length (x : Fin 7 → Nat) :
    (q8ResidueEdgeColors (q8ResidueList x)).length = 28 := by
  simp [q8ResidueEdgeColors, q8ResidueList, List.ofFn, Fin.foldr, Fin.foldr.loop]

lemma q8_mod28_mod7 (u : Nat) : (u % 28) % 7 = u % 7 := by
  omega

lemma q8PaperColorNat_mod7 (u v : Nat) :
    q8PaperColorNat u v % 7 =
      if u = 56 then v % 7
      else if v = 56 then u % 7
      else ((u + v + 1) / 2) % 7 := by
  by_cases hu : u = 56 <;> by_cases hv : v = 56 <;>
    simp [q8PaperColorNat, hu, hv]

lemma q8_mod14_pair_mod7 (u v : Nat) :
    ((u % 14 + v % 14 + 1) / 2) % 7 = ((u + v + 1) / 2) % 7 := by
  omega

lemma q8ResidueList_explicit (x : Fin 7 → Nat) :
    q8ResidueList x = [x 0 % 14, x 1 % 14, x 2 % 14, x 3 % 14,
      x 4 % 14, x 5 % 14, x 6 % 14] := by
  simp [q8ResidueList, List.ofFn, Fin.foldr, Fin.foldr.loop]

lemma q8Perm_cons_append {α : Type*} (a : α) (l : List α) :
    (a :: l).Perm (l ++ [a]) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    exact (List.Perm.swap b a l).trans (List.Perm.cons b ih)

lemma q8SevenBlockPerm (a0 a1 a2 a3 a4 a5 a6 : Nat)
    (e01 e02 e03 e04 e05 e06 e12 e13 e14 e15 e16
      e23 e24 e25 e26 e34 e35 e36 e45 e46 e56 : Nat) :
    List.Perm
      [a0,e01,e02,e03,e04,e05,e06,a1,e12,e13,e14,e15,e16,a2,e23,e24,e25,e26,
        a3,e34,e35,e36,a4,e45,e46,a5,e56,a6]
      [e01,e02,e03,e04,e05,e06,a0,e12,e13,e14,e15,e16,a1,e23,e24,e25,e26,a2,
        e34,e35,e36,a3,e45,e46,a4,e56,a5,a6] := by
  have h0 := q8Perm_cons_append a0 [e01,e02,e03,e04,e05,e06]
  have h1 := q8Perm_cons_append a1 [e12,e13,e14,e15,e16]
  have h2 := q8Perm_cons_append a2 [e23,e24,e25,e26]
  have h3 := q8Perm_cons_append a3 [e34,e35,e36]
  have h4 := q8Perm_cons_append a4 [e45,e46]
  have h5 := q8Perm_cons_append a5 [e56]
  have h6 := q8Perm_cons_append a6 []
  exact ((((((h0.append h1).append h2).append h3).append h4).append h5).append h6)

lemma q8ResidueEdgeColors_perm_pair_colors (x : Fin 7 → Nat)
    (hfin : ∀ i, x i < 56) :
    List.Perm (q8ResidueEdgeColors (q8ResidueList x))
      ((q8FinitePairColors (q8WithInfinity x)).map (fun c => c.val % 7)) := by
  have hne : ∀ i : Fin 7, x i ≠ 56 := by
    intro i hi
    have hx := hfin i
    omega
  rw [q8WithInfinity_eq, q8ResidueList_explicit]
  simpa [q8ResidueEdgeColors, q8FinitePairColors, q8Pairs,
    q8PaperColorNat_mod7, q8_mod14_pair_mod7, hne] using
    (q8SevenBlockPerm
      (x 0 % 7) (x 1 % 7) (x 2 % 7) (x 3 % 7) (x 4 % 7) (x 5 % 7) (x 6 % 7)
      ((x 0 + x 1 + 1) / 2 % 7) ((x 0 + x 2 + 1) / 2 % 7)
      ((x 0 + x 3 + 1) / 2 % 7) ((x 0 + x 4 + 1) / 2 % 7)
      ((x 0 + x 5 + 1) / 2 % 7) ((x 0 + x 6 + 1) / 2 % 7)
      ((x 1 + x 2 + 1) / 2 % 7) ((x 1 + x 3 + 1) / 2 % 7)
      ((x 1 + x 4 + 1) / 2 % 7) ((x 1 + x 5 + 1) / 2 % 7)
      ((x 1 + x 6 + 1) / 2 % 7) ((x 2 + x 3 + 1) / 2 % 7)
      ((x 2 + x 4 + 1) / 2 % 7) ((x 2 + x 5 + 1) / 2 % 7)
      ((x 2 + x 6 + 1) / 2 % 7) ((x 3 + x 4 + 1) / 2 % 7)
      ((x 3 + x 5 + 1) / 2 % 7) ((x 3 + x 6 + 1) / 2 % 7)
      ((x 4 + x 5 + 1) / 2 % 7) ((x 4 + x 6 + 1) / 2 % 7)
      ((x 5 + x 6 + 1) / 2 % 7))

lemma q8_mod7_count_le_four (l : List (Fin 28)) (hnd : l.Nodup)
    (hlen : l.length = 28) (r : Nat) :
    (l.map (fun c => c.val % 7)).count r ≤ 4 := by
  have hsu : l.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup hnd, hlen]
    decide
  have hfilter : (l.toFinset.filter (fun c : Fin 28 => c.val % 7 = r)).card ≤ 4 := by
    rw [hsu]
    by_cases hr : r < 7
    · interval_cases r <;> decide
    · have hz : (Finset.univ.filter (fun c : Fin 28 => c.val % 7 = r)).card = 0 := by
        apply Finset.card_eq_zero.mpr
        simp only [Finset.filter_eq_empty_iff]
        intro c hc
        omega
      rw [hz]
      omega
  have hcount :
      (l.map (fun c => c.val % 7)).count r =
        (l.toFinset.filter (fun c : Fin 28 => c.val % 7 = r)).card := by
    have hc := List.Nodup.card_eq_countP
      (P := fun c : Fin 28 => c.val % 7 = r) hnd
    change List.countP (fun z => z == r) (l.map (fun c : Fin 28 => c.val % 7)) = _
    rw [List.countP_map]
    have hp : (fun z => z == r) ∘ (fun c : Fin 28 => c.val % 7) =
        (fun c : Fin 28 => decide (c.val % 7 = r)) := by
      funext c
      dsimp
      by_cases h : c.val % 7 = r <;> simp [h]
    rw [hp]
    simpa using hc.symm
  rw [hcount]
  exact hfilter

theorem q8ResidueQuota_of_nodup (x : Fin 7 → Nat)
    (hfin : ∀ i, x i < 56)
    (hnd : (q8FinitePairColors (q8WithInfinity x)).Nodup) :
    q8ResidueQuota (q8ResidueList x) = true := by
  simp only [q8ResidueQuota, List.all_eq_true, decide_eq_true_eq]
  intro r hr
  have hp := q8ResidueEdgeColors_perm_pair_colors x hfin
  have hc := List.Perm.count_eq hp r
  rw [hc]
  exact q8_mod7_count_le_four _ hnd (q8FinitePairColors_length _) r

lemma q8ResidueOddOK_of_parity_sum (x : Fin 7 → Nat)
    (hodd : (x 0 % 2 + x 1 % 2 + x 2 % 2 + x 3 % 2 +
      x 4 % 2 + x 5 % 2 + x 6 % 2) = 3 ∨
      (x 0 % 2 + x 1 % 2 + x 2 % 2 + x 3 % 2 +
        x 4 % 2 + x 5 % 2 + x 6 % 2) = 4) :
    q8ResidueOddOK (q8ResidueList x) = true := by
  simp [q8ResidueOddOK, q8ResidueList_explicit]
  omega

/-- The mod-4 paper calculation: if the seven finite vertices have odd
residue count `r`, the infinity-branch colour sum is congruent to
`4 - (r + choose(r,2))` modulo 4.  The remaining bridge from the actual
colour sum to this congruence is kept separate from this tiny arithmetic fact.
-/
lemma q8OddResidue_candidates (r : Nat) (hr : r ≤ 7)
    (hmod : (4 - (r + r.choose 2) % 4) % 4 = 2) :
    r = 3 ∨ r = 4 := by
  interval_cases r <;> norm_num [Nat.choose] at hmod <;> omega

#print axioms q8ResidueEdgeColors_perm_pair_colors
#print axioms q8ResidueQuota_of_nodup
#print axioms q8OddResidue_candidates

end Erdos811
