import Q8PaperResidueSearch

/-! Kernel replay of the bounded residue classifier. This is not yet the
graph-to-residue bridge for arbitrary rainbow embeddings. -/

namespace Erdos811

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma q8ResidueBranch0 : q8ResidueCheck 5 0 [0,0] = true := by
  decide +kernel

#print axioms q8ResidueBranch0

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma q8ResidueBranch1 : q8ResidueCheck 5 1 [1,0] = true := by
  decide +kernel

#print axioms q8ResidueBranch1

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma q8ResidueBranch2 : q8ResidueCheck 5 2 [2,0] = true := by
  decide +kernel

#print axioms q8ResidueBranch2

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma q8ResidueBranch3 : q8ResidueCheck 5 3 [3,0] = true := by
  decide +kernel

#print axioms q8ResidueBranch3

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma q8ResidueBranch4 : q8ResidueCheck 5 4 [4,0] = true := by
  decide +kernel

#print axioms q8ResidueBranch4

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma q8ResidueBranch5 : q8ResidueCheck 5 5 [5,0] = true := by
  decide +kernel

#print axioms q8ResidueBranch5

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma q8ResidueBranch6 : q8ResidueCheck 5 6 [6,0] = true := by
  decide +kernel

#print axioms q8ResidueBranch6

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma q8ResidueBranch7 : q8ResidueCheck 5 7 [7,0] = true := by
  decide +kernel

#print axioms q8ResidueBranch7

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma q8ResidueBranch8 : q8ResidueCheck 5 8 [8,0] = true := by
  decide +kernel

#print axioms q8ResidueBranch8

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma q8ResidueBranch9 : q8ResidueCheck 5 9 [9,0] = true := by
  decide +kernel

#print axioms q8ResidueBranch9

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma q8ResidueBranch10 : q8ResidueCheck 5 10 [10,0] = true := by
  decide +kernel

#print axioms q8ResidueBranch10

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma q8ResidueBranch11 : q8ResidueCheck 5 11 [11,0] = true := by
  decide +kernel

#print axioms q8ResidueBranch11

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma q8ResidueBranch12 : q8ResidueCheck 5 12 [12,0] = true := by
  decide +kernel

#print axioms q8ResidueBranch12

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma q8ResidueBranch13 : q8ResidueCheck 5 13 [13,0] = true := by
  decide +kernel

#print axioms q8ResidueBranch13

theorem q8ResidueCheck_anchor_zero : q8ResidueCheck 6 0 [0] = true := by
  rw [q8ResidueCheck]
  apply List.all_eq_true.mpr
  intro v hv
  have hvlt := List.mem_range.mp hv
  interval_cases v <;>
    simp [q8ResidueBranch0, q8ResidueBranch1, q8ResidueBranch2, q8ResidueBranch3,
      q8ResidueBranch4, q8ResidueBranch5, q8ResidueBranch6, q8ResidueBranch7,
      q8ResidueBranch8, q8ResidueBranch9, q8ResidueBranch10, q8ResidueBranch11,
      q8ResidueBranch12, q8ResidueBranch13]

theorem q8ResidueClassify_anchor_zero (tail : List Nat) (hlen : tail.length = 6)
    (hvalid : q8ResidueContinuation 0 tail)
    (hquota : q8ResidueQuota (tail.reverse ++ [0]) = true)
    (hodd : q8ResidueOddOK (tail.reverse ++ [0]) = true) :
    tail.reverse ++ [0] ∈ q8ResidueTypes := by
  apply q8ResidueCheck_sound tail 0 [0] hvalid
  · simpa only [hlen] using q8ResidueCheck_anchor_zero
  · exact hquota
  · exact hodd

#print axioms q8ResidueClassify_anchor_zero

theorem q8ResidueClassify_anchor_zero_translation (tail : List Nat) (hlen : tail.length = 6)
    (hvalid : q8ResidueContinuation 0 tail)
    (hquota : q8ResidueQuota (tail.reverse ++ [0]) = true)
    (hodd : q8ResidueOddOK (tail.reverse ++ [0]) = true) :
    ∃ s : Fin 14, (tail.reverse ++ [0]).Perm
      ([2,4,7,9,11,12,13].map (fun v => (v + s.val) % 14)) := by
  exact q8ResidueTypes_translates _
    (q8ResidueClassify_anchor_zero tail hlen hvalid hquota hodd)

#print axioms q8ResidueClassify_anchor_zero_translation

end Erdos811
