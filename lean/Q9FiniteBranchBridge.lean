import Q9ParityObstructions
import Q9ParityCountBridge

/-! Arithmetic and counting glue for the finite branch of the anchored q=9
    argument.  The LRAT certificates only need the resulting two bounds and
    the parity value; all search-independent bookkeeping is proved here. -/

namespace Erdos811Q9FiniteBranchBridge

open Mathlib.Tactic.Sat
open Erdos811
open Erdos811Q9CNFSemantics
open Erdos811Q9ParityCountBridge
open Erdos811Q9SeqCounter

set_option maxHeartbeats 0 in
lemma finite_branch_count_identities
    {xs : List Nat} {g : Fin 9 ↪ Fin 73}
    (_hzero : g (0 : Fin 9) = 0)
    (hcoverage : ∀ z, z ∈ xs → ∃ i : Fin 9, z = (g i).val)
    (himage : ∀ i : Fin 9, (g i).val ∈ xs)
    (hbound : ∀ z, z ∈ xs → z < 73)
    (hcard : 9 ≤ xs.toFinset.card) :
    prefixCount (q9OddSelectionBool xs) 36 =
        ∑ i : Fin 9, (g i).val % 2 ∧
      prefixCount (fun i => !(selectionBool xs i)) 73 ≤ 64 := by
  have hparity : prefixCount (q9OddSelectionBool xs) 36 =
      ∑ i : Fin 9, (g i).val % 2 := by
    simpa using (odd_prefixCount_eq_parity_sum hcoverage himage)
  have hbase : prefixCount (fun i => !(selectionBool xs i)) 73 ≤ 64 :=
    base_prefixCount_le_of_card hbound hcard
  exact ⟨hparity, hbase⟩

/- The finite branch has at most eight odd vertices because the anchored
   vertex `g 0 = 0` is even.  This helper packages that elementary bound and
   the accompanying `choose` estimate needed by the modular obstruction. -/
set_option maxHeartbeats 0 in
lemma finite_branch_choose_bound
    {g : Fin 9 ↪ Fin 73}
    {r s : Nat}
    (hrsum : r = ∑ i : Fin 9, (g i).val % 2)
    (hs : s = ∑ i : Fin 9, ((g i).val + 1) / 2)
    (hr : r ≤ 8) : r.choose 2 ≤ 8 * s := by
  have hbit : ∀ i : Fin 9, (g i).val % 2 ≤ ((g i).val + 1) / 2 := by
    intro i
    omega
  have hsum :
      (∑ i : Fin 9, (g i).val % 2) ≤
        ∑ i : Fin 9, ((g i).val + 1) / 2 := by
    exact Finset.sum_le_sum (fun i hi => hbit i)
  have hrs : r ≤ s := by
    rw [hrsum, hs]
    exact hsum
  have hchoose : r.choose 2 ≤ 8 * r := by
    rw [Nat.choose_two_right]
    calc
      r * (r - 1) / 2 ≤ r * (r - 1) := Nat.div_le_self _ _
      _ ≤ r * 8 := Nat.mul_le_mul_left r (by omega)
      _ = 8 * r := Nat.mul_comm _ _
  omega

/- Direct endpoint for the finite branch: once the rainbow hypotheses and the
   coverage/count identities are available, the paper-level parity argument
   produces exactly the `r = 4 ∨ r = 5` disjunction consumed by the LRAT
   semantic bridge. -/
set_option maxHeartbeats 0 in
lemma finite_branch_candidate_of_counts
    {xs : List Nat} {g : Fin 9 ↪ Fin 73}
    (hzero : g (0 : Fin 9) = 0)
    (hfin : ∀ i : Fin 9, (g i).val < 72)
    (hf : ∀ ⦃a b c d : Fin 9⦄,
      (SimpleGraph.completeGraph (Fin 9)).Adj a b →
      (SimpleGraph.completeGraph (Fin 9)).Adj c d →
      ¬ SameUndirectedEdge (g a) (g b) (g c) (g d) →
      q9Coloring.color (g a) (g b) ≠ q9Coloring.color (g c) (g d))
    (hcoverage : ∀ z, z ∈ xs → ∃ i : Fin 9, z = (g i).val)
    (himage : ∀ i : Fin 9, (g i).val ∈ xs)
    (hbound : ∀ z, z ∈ xs → z < 73)
    (hcard : 9 ≤ xs.toFinset.card) :
    let r := prefixCount (q9OddSelectionBool xs) 36
    r = 4 ∨ r = 5 := by
  let r : Nat := prefixCount (q9OddSelectionBool xs) 36
  let s : Nat := ∑ i : Fin 9, ((g i).val + 1) / 2
  have hcounts := finite_branch_count_identities
    (xs := xs) (g := g) hzero hcoverage himage hbound hcard
  have hparity : r = ∑ i : Fin 9, (g i).val % 2 := by
    simpa [r] using hcounts.1
  have hs : s = ∑ i : Fin 9, ((g i).val + 1) / 2 := by
    rfl
  have hrbit : ∀ i : Fin 9, (g i).val % 2 ≤ 1 := by
    intro i
    omega
  have hzeroParity : (g (0 : Fin 9)).val % 2 = 0 := by
    simp [hzero]
  have hsumErase :
      (Finset.univ.erase (0 : Fin 9)).sum
          (fun i : Fin 9 => (g i).val % 2) ≤ 8 := by
    have hsum := Finset.sum_le_card_nsmul
      (Finset.univ.erase (0 : Fin 9))
      (fun i : Fin 9 => (g i).val % 2) 1
      (by intro i hi; exact hrbit i)
    have hcardErase : (Finset.univ.erase (0 : Fin 9)).card = 8 := by decide
    simpa [hcardErase, nsmul_eq_mul] using hsum
  have hdecomp := Finset.sum_erase_add (Finset.univ : Finset (Fin 9))
    (fun i : Fin 9 => (g i).val % 2) (Finset.mem_univ (0 : Fin 9))
  have hr : r ≤ 8 := by
    rw [hparity]
    rw [← hdecomp]
    rw [hzeroParity]
    exact hsumErase
  have hc : r.choose 2 ≤ 8 * s :=
    finite_branch_choose_bound hparity hs hr
  exact q9_finite_branch_candidate hfin hf r s hr hc hs hparity

end Erdos811Q9FiniteBranchBridge
