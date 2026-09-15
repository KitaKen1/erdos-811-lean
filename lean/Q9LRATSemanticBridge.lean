import Q9ConstructiveCNFAssembly
import Q9SATtoGraph
import Q9ParityCountBridge

/-!
  Semantic endpoint for the q=9 r=4 LRAT certificate.

  The large proof-producing replay is intentionally supplied as an argument:
  this file verifies the small, reusable step that turns such a proof of the
  empty clause into a contradiction for any edge-distinct selection satisfying
  the finite-counter encoding hypotheses.  The staged replay can therefore be
  compiled independently and plugged in at the final stage.
-/

namespace Erdos811Q9LRATSemanticBridge

open Mathlib.Tactic.Sat
open Erdos811
open Erdos811Q9CNFSemantics
open Erdos811Q9ConstructiveCNFAssembly
open Erdos811Q9ParityCountBridge
open Erdos811Q9SeqCounter

lemma odd_complement_prefixCount_add
    (ys : List Nat) :
    prefixCount (q9OddComplementBool ys) 36 +
        prefixCount (q9OddSelectionBool ys) 36 = 36 := by
  unfold prefixCount
  rw [← Finset.sum_add_distrib]
  have hpoint (j : Nat) :
      (if q9OddComplementBool ys j = true then 1 else 0) +
          (if q9OddSelectionBool ys j = true then 1 else 0) = 1 := by
    by_cases h : q9OddSelectionBool ys j = true <;>
      simp [q9OddComplementBool, h]
  have hsum :
      (∑ j ∈ (Finset.range 36),
        ((if q9OddComplementBool ys j = true then 1 else 0) +
          (if q9OddSelectionBool ys j = true then 1 else 0))) =
        ∑ j ∈ (Finset.range 36), 1 := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hpoint j
  rw [hsum]
  simp

lemma odd_complement_prefixCount_le_of_selection_ge
    {ys : List Nat} {k : Nat}
    (hk : k ≤ prefixCount (q9OddSelectionBool ys) 36) :
    prefixCount (q9OddComplementBool ys) 36 ≤ 36 - k := by
  have hsum := odd_complement_prefixCount_add ys
  omega

lemma r4_lrat_false_of_constructive
    {xs : List Nat}
    (hproof : Erdos811Q9NoInfR4CNF.q9_noinf_r4_ctx.proof [])
    (hdist : q9EdgeDistinct xs)
    (hbaseCount : prefixCount (fun i => !(selectionBool xs i)) 73 ≤ 64)
    (hatleastCount : prefixCount (q9OddComplementBool xs) 36 ≤ 32)
    (hatmostCount : prefixCount (q9OddSelectionBool xs) 36 ≤ 4)
    (h0 : 0 ∈ xs) (h72 : 72 ∉ xs) : False := by
  apply Erdos811Q9SATtoGraph.false_of_fmla_proof hproof
  exact Erdos811Q9ConstructiveCNFAssembly.q9_r4_cnf_satisfied_constructive
    hdist hbaseCount hatleastCount hatmostCount h0 h72

#print axioms r4_lrat_false_of_constructive

lemma false_of_lrat_r4_or_r5
    {ys : List Nat} {r : Nat}
    (hproof4 : Erdos811Q9NoInfR4CNF.q9_noinf_r4_ctx.proof [])
    (hproof5 : Erdos811Q9NoInfR5CNF.q9_noinf_r5_ctx.proof [])
    (hdist : q9EdgeDistinct ys)
    (hbaseCount : prefixCount (fun i => !(selectionBool ys i)) 73 ≤ 64)
    (hparity : prefixCount (q9OddSelectionBool ys) 36 = r)
    (hodd : r = 4 ∨ r = 5)
    (h0 : 0 ∈ ys) (h72 : 72 ∉ ys) : False := by
  rcases hodd with hodd | hodd
  · have hsel : prefixCount (q9OddSelectionBool ys) 36 ≤ 4 := by
      rw [hparity, hodd]
    have hcomp : prefixCount (q9OddComplementBool ys) 36 ≤ 32 := by
      have hge : 4 ≤ prefixCount (q9OddSelectionBool ys) 36 := by
        rw [hparity, hodd]
      have h := odd_complement_prefixCount_le_of_selection_ge hge
      omega
    exact r4_lrat_false_of_constructive hproof4 hdist hbaseCount hcomp hsel h0 h72
  · have hsel : prefixCount (q9OddSelectionBool ys) 36 ≤ 5 := by
      rw [hparity, hodd]
    have hcomp : prefixCount (q9OddComplementBool ys) 36 ≤ 31 := by
      have hge : 5 ≤ prefixCount (q9OddSelectionBool ys) 36 := by
        rw [hparity, hodd]
      have h := odd_complement_prefixCount_le_of_selection_ge hge
      omega
    exact Erdos811Q9SATtoGraph.false_of_fmla_proof hproof5
      (Erdos811Q9ConstructiveCNFAssembly.q9_r5_cnf_satisfied_constructive
        hdist hbaseCount hcomp hsel h0 h72)

end Erdos811Q9LRATSemanticBridge
