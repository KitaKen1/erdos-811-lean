import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Paper-style arithmetic reductions for the q = 8 cyclic base.

This file deliberately isolates the part of the q = 8 proof which does not
need the large DFS certificate: when all eight chosen vertices are finite,
the total colour sum modulo 7 already gives an impossible parity count.
-/

namespace Erdos811

/-- The numerical cyclic colour; its agreement with `q8Coloring` is checked in `Q8Paper`. -/
def q8PaperColorNat (i j : Nat) : Nat :=
  if i = 56 then j % 28
  else if j = 56 then i % 28
  else ((i + j + 1) / 2) % 28

def q8Pairs : List (Fin 8 × Fin 8) :=
  [ (0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7),
    (1,2), (1,3), (1,4), (1,5), (1,6), (1,7),
    (2,3), (2,4), (2,5), (2,6), (2,7),
    (3,4), (3,5), (3,6), (3,7),
    (4,5), (4,6), (4,7),
    (5,6), (5,7),
    (6,7) ]

def q8PairSum (F : Fin 8 → Int) : Int :=
  (q8Pairs.map (fun ij => F ij.1 + F ij.2)).sum

def q8PairProducts (e : Fin 8 → Int) : Int :=
  (q8Pairs.map (fun ij => e ij.1 * e ij.2)).sum

def q8VertexSum (F : Fin 8 → Int) : Int :=
  F 0 + F 1 + F 2 + F 3 + F 4 + F 5 + F 6 + F 7

lemma q8VertexSum_eq_sum (F : Fin 8 → Int) : q8VertexSum F = ∑ i : Fin 8, F i := by
  simp [q8VertexSum, Fin.sum_univ_succ]
  ring

lemma q8PairSum_eq_seven_sum (F : Fin 8 → Int) :
    q8PairSum F = 7 * q8VertexSum F := by
  simp [q8PairSum, q8Pairs, q8VertexSum]
  ring

set_option maxHeartbeats 0 in
lemma q8PairProducts_eq_choose (e : Fin 8 → Int)
    (he : ∀ i, e i = 0 ∨ e i = 1) :
    q8PairProducts e =
      (q8VertexSum e * (q8VertexSum e - 1)) / 2 := by
  have hsq : q8VertexSum e * q8VertexSum e =
      q8VertexSum e + 2 * q8PairProducts e := by
    simp only [q8VertexSum, q8PairProducts, q8Pairs]
    ring_nf
    have h0 : e 0 ^ 2 = e 0 := by
      rcases he 0 with h | h <;> simp [h]
    have h1 : e 1 ^ 2 = e 1 := by
      rcases he 1 with h | h <;> simp [h]
    have h2 : e 2 ^ 2 = e 2 := by
      rcases he 2 with h | h <;> simp [h]
    have h3 : e 3 ^ 2 = e 3 := by
      rcases he 3 with h | h <;> simp [h]
    have h4 : e 4 ^ 2 = e 4 := by
      rcases he 4 with h | h <;> simp [h]
    have h5 : e 5 ^ 2 = e 5 := by
      rcases he 5 with h | h <;> simp [h]
    have h6 : e 6 ^ 2 = e 6 := by
      rcases he 6 with h | h <;> simp [h]
    have h7 : e 7 ^ 2 = e 7 := by
      rcases he 7 with h | h <;> simp [h]
    simp [h0, h1, h2, h3, h4, h5, h6, h7]
    ring_nf
  symm
  apply Int.ediv_eq_of_eq_mul_left (by norm_num : (2 : Int) ≠ 0)
  nlinarith [hsq]

lemma q8FiniteEdgeFormula (x y : Nat) (hx : x < 56) (hy : y < 56) :
    q8PaperColorNat x y =
      ((x + 1) / 2 + (y + 1) / 2 - (x % 2) * (y % 2)) % 28 := by
  have hx56 : x ≠ 56 := by omega
  have hy56 : y ≠ 56 := by omega
  simp [q8PaperColorNat, hx56, hy56]
  congr 1
  have hxm : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have hym : y % 2 = 0 ∨ y % 2 = 1 := by omega
  rcases hxm with hxm | hxm <;> rcases hym with hym | hym <;>
    simp [hxm, hym] <;>
  omega

set_option maxHeartbeats 0 in
lemma q8FiniteEdgeParityFormula (x y : Nat) (hx : x < 56) (hy : y < 56) :
    q8PaperColorNat x y % 2 =
      (((x % 4) + (y % 4) + 1) / 2) % 2 := by
  have hx56 : x ≠ 56 := by omega
  have hy56 : y ≠ 56 := by omega
  have hxm : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  have hym : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
  rcases hxm with hxm | hxm | hxm | hxm <;>
    rcases hym with hym | hym | hym | hym <;>
      simp [q8PaperColorNat, hx56, hy56, hxm, hym] <;> omega

def q8ResidueCount (r : Fin 8 → Fin 4) (k : Fin 4) : Nat :=
  (Finset.univ.filter (fun i => r i = k)).card

def q8OddPairWeight (r : Fin 8 → Fin 4) : Int :=
  (q8Pairs.map (fun ij =>
    if (((r ij.1).val + (r ij.2).val + 1) / 2) % 2 = 1 then (1 : Int) else 0)).sum

def q8PairCross (e f : Fin 8 → Int) : Int :=
  (q8Pairs.map (fun ij => e ij.1 * f ij.2 + f ij.1 * e ij.2)).sum

def q8PairDiag (e f : Fin 8 → Int) : Int :=
  e 0 * f 0 + e 1 * f 1 + e 2 * f 2 + e 3 * f 3 +
    e 4 * f 4 + e 5 * f 5 + e 6 * f 6 + e 7 * f 7

lemma q8PairCross_add_diag_eq_mul (e f : Fin 8 → Int) :
    q8PairCross e f + q8PairDiag e f = q8VertexSum e * q8VertexSum f := by
  simp [q8PairCross, q8PairDiag, q8Pairs, q8VertexSum]
  ring

lemma q8PairCross_eq_mul (e f : Fin 8 → Int)
    (hdiag : ∀ i, e i * f i = 0) :
    q8PairCross e f = q8VertexSum e * q8VertexSum f := by
  have h0 := hdiag 0
  have h1 := hdiag 1
  have h2 := hdiag 2
  have h3 := hdiag 3
  have h4 := hdiag 4
  have h5 := hdiag 5
  have h6 := hdiag 6
  have h7 := hdiag 7
  have hd : q8PairDiag e f = 0 := by
    simp [q8PairDiag, h0, h1, h2, h3, h4, h5, h6, h7]
  rw [← q8PairCross_add_diag_eq_mul e f]
  simp [hd]

def q8ResidueIndicator (r : Fin 8 → Fin 4) (k : Fin 4) (i : Fin 8) : Int :=
  if r i = k then 1 else 0

lemma q8ResidueIndicator_sum (r : Fin 8 → Fin 4) (k : Fin 4) :
    q8VertexSum (q8ResidueIndicator r k) = q8ResidueCount r k := by
  have hc := Finset.sum_boole (R := Int) (fun i : Fin 8 => r i = k) Finset.univ
  rw [q8VertexSum_eq_sum]
  simpa [q8ResidueCount, q8ResidueIndicator] using hc

set_option maxHeartbeats 0 in
lemma q8OddPairWeight_formula (r : Fin 8 → Fin 4) :
    q8OddPairWeight r =
      q8PairCross (q8ResidueIndicator r 0) (q8ResidueIndicator r 1) +
      q8PairCross (q8ResidueIndicator r 0) (q8ResidueIndicator r 2) +
      q8PairCross (q8ResidueIndicator r 2) (q8ResidueIndicator r 3) +
      q8PairProducts (q8ResidueIndicator r 1) +
      q8PairProducts (q8ResidueIndicator r 3) := by
  have hpoint : ∀ ij ∈ q8Pairs,
      (if (((r ij.1).val + (r ij.2).val + 1) / 2) % 2 = 1 then (1 : Int) else 0) =
        q8ResidueIndicator r 0 ij.1 * q8ResidueIndicator r 1 ij.2 +
        q8ResidueIndicator r 1 ij.1 * q8ResidueIndicator r 0 ij.2 +
        q8ResidueIndicator r 0 ij.1 * q8ResidueIndicator r 2 ij.2 +
        q8ResidueIndicator r 2 ij.1 * q8ResidueIndicator r 0 ij.2 +
        q8ResidueIndicator r 2 ij.1 * q8ResidueIndicator r 3 ij.2 +
        q8ResidueIndicator r 3 ij.1 * q8ResidueIndicator r 2 ij.2 +
        q8ResidueIndicator r 1 ij.1 * q8ResidueIndicator r 1 ij.2 +
        q8ResidueIndicator r 3 ij.1 * q8ResidueIndicator r 3 ij.2 := by
    intro ij hij
    generalize hi : r ij.1 = ri
    generalize hj : r ij.2 = rj
    fin_cases ri <;> fin_cases rj <;>
      simp [q8ResidueIndicator, hi, hj]
  have hmap := List.map_congr_left hpoint
  have hsum := congrArg List.sum hmap
  simpa [q8OddPairWeight, q8PairCross, q8PairProducts, List.sum_map_add,
    add_assoc] using hsum

lemma q8OddPairWeight_formula_counts (r : Fin 8 → Fin 4) :
    q8OddPairWeight r =
      (q8ResidueCount r 0 : Int) * q8ResidueCount r 1 +
      (q8ResidueCount r 0 : Int) * q8ResidueCount r 2 +
      (q8ResidueCount r 2 : Int) * q8ResidueCount r 3 +
      ((q8ResidueCount r 1 : Int) * (q8ResidueCount r 1 - 1)) / 2 +
      ((q8ResidueCount r 3 : Int) * (q8ResidueCount r 3 - 1)) / 2 := by
  rw [q8OddPairWeight_formula]
  have h01 := q8PairCross_eq_mul (q8ResidueIndicator r 0)
    (q8ResidueIndicator r 1) (by
      intro i
      simp only [q8ResidueIndicator]
      by_cases h0 : r i = 0 <;> by_cases h1 : r i = 1 <;> simp [h0, h1])
  have h02 := q8PairCross_eq_mul (q8ResidueIndicator r 0)
    (q8ResidueIndicator r 2) (by
      intro i
      simp only [q8ResidueIndicator]
      by_cases h0 : r i = 0 <;> by_cases h2 : r i = 2 <;> simp [h0, h2])
  have h23 := q8PairCross_eq_mul (q8ResidueIndicator r 2)
    (q8ResidueIndicator r 3) (by
      intro i
      simp only [q8ResidueIndicator]
      by_cases h2 : r i = 2 <;> by_cases h3 : r i = 3 <;> simp [h2, h3])
  have h11 := q8PairProducts_eq_choose (q8ResidueIndicator r 1) (by
    intro i
    by_cases h : r i = 1 <;> simp [q8ResidueIndicator, h])
  have h33 := q8PairProducts_eq_choose (q8ResidueIndicator r 3) (by
    intro i
    by_cases h : r i = 3 <;> simp [q8ResidueIndicator, h])
  rw [h01, h02, h23, h11, h33]
  simp only [q8ResidueIndicator_sum]

lemma q8_cast_choose_two (n : Nat) :
    (n.choose 2 : Int) = (n : Int) * (n - 1) / 2 := by
  cases n with
  | zero => norm_num [Nat.choose]
  | succ n =>
    rw [Nat.choose_two_right]
    norm_num

lemma q8ResidueCount_sum (r : Fin 8 → Fin 4) :
    q8ResidueCount r 0 + q8ResidueCount r 1 +
      q8ResidueCount r 2 + q8ResidueCount r 3 = 8 := by
  have hsum :
      q8VertexSum (q8ResidueIndicator r 0) +
        q8VertexSum (q8ResidueIndicator r 1) +
      q8VertexSum (q8ResidueIndicator r 2) +
        q8VertexSum (q8ResidueIndicator r 3) =
          ∑ i : Fin 8, (1 : Int) := by
    rw [q8VertexSum_eq_sum, q8VertexSum_eq_sum, q8VertexSum_eq_sum,
      q8VertexSum_eq_sum]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    generalize ri : r i = rv
    fin_cases rv <;>
      simp [q8ResidueIndicator, ri]
  have hsum' :
      (q8ResidueCount r 0 + q8ResidueCount r 1 +
        q8ResidueCount r 2 + q8ResidueCount r 3 : Int) = 8 := by
    calc
      _ = ∑ i : Fin 8, (1 : Int) := by
        simpa only [q8ResidueIndicator_sum] using hsum
      _ = 8 := by norm_num
  exact_mod_cast hsum'

lemma q8OddPairWeight_eq_nat_cast (r : Fin 8 → Fin 4) :
    q8OddPairWeight r =
      (q8ResidueCount r 0 * q8ResidueCount r 1 +
        q8ResidueCount r 0 * q8ResidueCount r 2 +
        q8ResidueCount r 2 * q8ResidueCount r 3 +
        (q8ResidueCount r 1).choose 2 +
        (q8ResidueCount r 3).choose 2 : Int) := by
  rw [q8OddPairWeight_formula_counts]
  rw [q8_cast_choose_two, q8_cast_choose_two]

lemma q8_choose_candidates (r : Nat) (hr : r ≤ 8)
    (hm : r.choose 2 % 7 = 0) : r = 0 ∨ r = 1 ∨ r = 7 ∨ r = 8 := by
  interval_cases r <;> norm_num [Nat.choose] at hm <;> omega

set_option maxHeartbeats 0 in
lemma q8_count_obstruction (n0 n1 n2 n3 : Nat)
    (hsum : n0 + n1 + n2 + n3 = 8)
    (hmod : (n1 + n3).choose 2 % 7 = 0)
    (hodd : n0 * n1 + n0 * n2 + n2 * n3 +
      n1.choose 2 + n3.choose 2 = 14) : False := by
  have hr : n1 + n3 ≤ 8 := by omega
  have hc := q8_choose_candidates (n1 + n3) hr hmod
  rcases hc with h0 | h1 | h7 | h8
  · have hn1 : n1 = 0 := by omega
    have hn3 : n3 = 0 := by omega
    subst n1
    subst n3
    have hn0 : n0 ≤ 8 := by omega
    interval_cases n0 <;> norm_num [Nat.choose] at * <;> omega
  · have hn1le : n1 ≤ 1 := by omega
    have hn0 : n0 ≤ 8 := by omega
    have hn3 : n3 = 1 - n1 := by omega
    subst n3
    interval_cases n1 <;> interval_cases n0 <;>
      norm_num [Nat.choose] at * <;> omega
  · have hn1le : n1 ≤ 7 := by omega
    have hn0 : n0 ≤ 8 := by omega
    have hn3 : n3 = 7 - n1 := by omega
    subst n3
    interval_cases n1 <;> interval_cases n0 <;>
      norm_num [Nat.choose] at * <;> omega
  · have hn1le : n1 ≤ 8 := by omega
    have hn0 : n0 ≤ 8 := by omega
    have hn3 : n3 = 8 - n1 := by omega
    subst n3
    interval_cases n1 <;> interval_cases n0 <;>
      norm_num [Nat.choose] at * <;> omega

lemma q8PaperColorNat_lt_28 (x y : Nat) : q8PaperColorNat x y < 28 := by
  unfold q8PaperColorNat
  split
  · omega
  · split <;> omega

lemma q8Pairs_ordered : ∀ p : Fin 8 × Fin 8, p ∈ q8Pairs → p.1 < p.2 := by
  decide

lemma q8Pairs_nodup : q8Pairs.Nodup := by decide

lemma list_pairwise_of_mem_ne {α : Type*} {R : α → α → Prop}
    {l : List α} (hnodup : l.Nodup)
    (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b) : l.Pairwise R := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.pairwise_cons]
      constructor
      · intro b hb
        apply h a (by simp) b (by simp [hb])
        intro hab
        subst b
        exact (List.nodup_cons.mp hnodup).1 hb
      · apply ih (List.nodup_cons.mp hnodup).2
        intro x hx y hy hxy
        exact h x (by simp [hx]) y (by simp [hy]) hxy

def q8FinitePairColors (x : Fin 8 → Nat) : List (Fin 28) :=
  q8Pairs.map (fun ij =>
    ⟨q8PaperColorNat (x ij.1) (x ij.2), q8PaperColorNat_lt_28 _ _⟩)

lemma q8FiniteEdge_mod7 (x y : Nat) (hx : x < 56) (hy : y < 56) :
    q8PaperColorNat x y ≡
      ((x + 1) / 2 + (y + 1) / 2 - (x % 2) * (y % 2)) [MOD 7] := by
  rw [q8FiniteEdgeFormula x y hx hy]
  simp [Nat.ModEq, Nat.mod_mod_of_dvd _ (by norm_num : 7 ∣ 28)]

def q8PairB (x : Fin 8 → Nat) (ij : Fin 8 × Fin 8) : Nat :=
  (x ij.1 + 1) / 2 + (x ij.2 + 1) / 2 -
    (x ij.1 % 2) * (x ij.2 % 2)

set_option maxHeartbeats 0 in
lemma q8FinitePairB_mod_sum (x : Fin 8 → Nat)
    (hfin : ∀ i, x i < 56) :
    (q8Pairs.map (fun ij => q8PaperColorNat (x ij.1) (x ij.2))).sum ≡
      (q8Pairs.map (q8PairB x)).sum [MOD 7] := by
  have hsum := Nat.ModEq.sum (s := q8Pairs.toFinset)
    (f := fun ij => q8PaperColorNat (x ij.1) (x ij.2))
    (g := q8PairB x) (by
      intro ij hij
      apply q8FiniteEdge_mod7
      · exact hfin ij.1
      · exact hfin ij.2)
  rw [← List.sum_toFinset
    (f := fun ij => q8PaperColorNat (x ij.1) (x ij.2)) q8Pairs_nodup]
  rw [← List.sum_toFinset (f := q8PairB x) q8Pairs_nodup]
  exact hsum

set_option maxHeartbeats 0 in
lemma q8FinitePairB_mod_sum_colors (x : Fin 8 → Nat)
    (hfin : ∀ i, x i < 56) :
    ((q8FinitePairColors x).map (fun c => c.val)).sum ≡
      (q8Pairs.map (q8PairB x)).sum [MOD 7] := by
  have hmap : (q8FinitePairColors x).map (fun c => c.val) =
      q8Pairs.map (fun ij => q8PaperColorNat (x ij.1) (x ij.2)) := by
    rfl
  rw [hmap]
  exact q8FinitePairB_mod_sum x hfin

lemma q8FinitePairColors_length (x : Fin 8 → Nat) :
    (q8FinitePairColors x).length = 28 := by
  rfl

lemma q8FinitePairColors_sum (x : Fin 8 → Nat)
    (hnd : (q8FinitePairColors x).Nodup) :
    ((q8FinitePairColors x).map (fun c => c.val)).sum = 378 := by
  let s : Finset (Fin 28) := (q8FinitePairColors x).toFinset
  have hcard : s.card = 28 := by
    rw [show s = (q8FinitePairColors x).toFinset by rfl]
    rw [List.toFinset_card_of_nodup hnd]
    simp [q8FinitePairColors_length]
  have hs : s = Finset.univ := Finset.eq_univ_of_card s (by simpa using hcard)
  calc
    ((q8FinitePairColors x).map (fun c => c.val)).sum =
        s.sum (fun c : Fin 28 => c.val) :=
      (List.sum_toFinset (f := fun c : Fin 28 => c.val) hnd).symm
    _ = ∑ c : Fin 28, c.val := by rw [hs]
    _ = 378 := by decide

def q8FiniteOddColorCount (x : Fin 8 → Nat) : Nat :=
  ((q8FinitePairColors x).map (fun c => if c.val % 2 = 1 then 1 else 0)).sum

lemma q8FiniteOddColorCount_eq_fourteen (x : Fin 8 → Nat)
    (hnd : (q8FinitePairColors x).Nodup) :
    q8FiniteOddColorCount x = 14 := by
  let s : Finset (Fin 28) := (q8FinitePairColors x).toFinset
  have hcard : s.card = 28 := by
    rw [show s = (q8FinitePairColors x).toFinset by rfl]
    rw [List.toFinset_card_of_nodup hnd]
    simp [q8FinitePairColors_length]
  have hs : s = Finset.univ := Finset.eq_univ_of_card s (by simpa using hcard)
  calc
    q8FiniteOddColorCount x = s.sum (fun c : Fin 28 => if c.val % 2 = 1 then 1 else 0) :=
      (List.sum_toFinset (f := fun c : Fin 28 => if c.val % 2 = 1 then 1 else 0) hnd).symm
    _ = ∑ c : Fin 28, if c.val % 2 = 1 then 1 else 0 := by rw [hs]
    _ = 14 := by decide

lemma q8FinitePaperParityObstruction (r : Fin 8 → Fin 4)
    (hmod : (q8ResidueCount r 1 + q8ResidueCount r 3).choose 2 % 7 = 0) :
    q8OddPairWeight r ≠ 14 := by
  intro hodd
  rw [q8OddPairWeight_eq_nat_cast] at hodd
  apply q8_count_obstruction (q8ResidueCount r 0) (q8ResidueCount r 1)
    (q8ResidueCount r 2) (q8ResidueCount r 3)
  · exact q8ResidueCount_sum r
  · exact hmod
  · exact_mod_cast hodd

/- The next lemmas expose the remaining finite-branch connection in a
small, search-free interface.  The first identity is the paper's
`a_i+a_j-ε_iε_j` decomposition; the second counts each vertex seven times. -/

lemma q8PairB_add_oddProduct (x : Fin 8 → Nat) (ij : Fin 8 × Fin 8) :
    q8PairB x ij + (x ij.1 % 2) * (x ij.2 % 2) =
      (x ij.1 + 1) / 2 + (x ij.2 + 1) / 2 := by
  dsimp [q8PairB]
  have hi : x ij.1 % 2 = 0 ∨ x ij.1 % 2 = 1 := by omega
  have hj : x ij.2 % 2 = 0 ∨ x ij.2 % 2 = 1 := by omega
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    simp [hi, hj] <;> omega

lemma q8PairSumNat_eq_seven_sum (F : Fin 8 → Nat) :
    (q8Pairs.map (fun ij => F ij.1 + F ij.2)).sum =
      7 * (F 0 + F 1 + F 2 + F 3 + F 4 + F 5 + F 6 + F 7) := by
  simp only [q8Pairs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd]
  ring

lemma q8PairB_sum_add_oddProducts (x : Fin 8 → Nat) :
    (q8Pairs.map (q8PairB x)).sum +
        (q8Pairs.map (fun ij => (x ij.1 % 2) * (x ij.2 % 2))).sum =
      7 * ((x 0 + 1) / 2 + (x 1 + 1) / 2 + (x 2 + 1) / 2 +
        (x 3 + 1) / 2 + (x 4 + 1) / 2 + (x 5 + 1) / 2 +
        (x 6 + 1) / 2 + (x 7 + 1) / 2) := by
  calc
    (q8Pairs.map (q8PairB x)).sum +
          (q8Pairs.map (fun ij => (x ij.1 % 2) * (x ij.2 % 2))).sum =
        (q8Pairs.map (fun ij => q8PairB x ij +
          (x ij.1 % 2) * (x ij.2 % 2))).sum := by
      rw [List.sum_map_add]
    _ = (q8Pairs.map (fun ij =>
          (x ij.1 + 1) / 2 + (x ij.2 + 1) / 2)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro ij hij
      exact q8PairB_add_oddProduct x ij
    _ = 7 * ((x 0 + 1) / 2 + (x 1 + 1) / 2 + (x 2 + 1) / 2 +
        (x 3 + 1) / 2 + (x 4 + 1) / 2 + (x 5 + 1) / 2 +
        (x 6 + 1) / 2 + (x 7 + 1) / 2) := by
      exact q8PairSumNat_eq_seven_sum (fun i => (x i + 1) / 2)

lemma q8FinitePairB_mod_zero_of_color_sum (x : Fin 8 → Nat)
    (hfin : ∀ i, x i < 56)
    (hcolor_sum : ((q8FinitePairColors x).map (fun c => c.val)).sum = 378) :
    (q8Pairs.map (q8PairB x)).sum % 7 = 0 := by
  have h := q8FinitePairB_mod_sum_colors x hfin
  rw [hcolor_sum] at h
  have hm : 378 % 7 = (q8Pairs.map (q8PairB x)).sum % 7 := by
    simpa [Nat.ModEq] using h
  norm_num at hm
  omega

lemma q8FinitePaperContradiction_of_mod7_and_distinct
    (x : Fin 8 → Nat) (hfin : ∀ i, x i < 56)
    (hnd : (q8FinitePairColors x).Nodup)
    (r : Fin 8 → Fin 4)
    (hmod : (q8ResidueCount r 1 + q8ResidueCount r 3).choose 2 % 7 = 0)
    (hparity : q8OddPairWeight r = (q8FiniteOddColorCount x : Int)) : False := by
  have hodd : q8FiniteOddColorCount x = 14 :=
    q8FiniteOddColorCount_eq_fourteen x hnd
  have hodd' : q8OddPairWeight r = 14 := by
    rw [hparity]
    exact_mod_cast hodd
  exact (q8FinitePaperParityObstruction r hmod) hodd'

end Erdos811
