import Q9CollisionBoundsAudit
import Q9ConstructiveValuation

/-! Assembly of the constructive q=9 finite-branch valuation.

The large collision prefix is consumed through the balanced-tree audit
lemmas.  The remaining DIMACS slices are discharged by the sequential-counter
semantics, using the finite-prefix decoder in `Q9ConstructiveValuation`.
The resulting block-soundness theorems expose all five semantic components
without re-evaluating the 94,608-clause list as one giant proposition.
-/

namespace Erdos811Q9ConstructiveCNFAssembly

open Mathlib.Tactic.Sat
open Erdos811
open Erdos811Q9SeqCounter
open Erdos811Q9CNFSemantics
open Erdos811Q9CNFBridge
open Erdos811Q9ConstructiveValuation
open Erdos811Q9CollisionBoundsAuditR4
open Erdos811Q9CollisionBoundsAuditR5

lemma q9_r4_anchor_satisfied_constructive {xs : List Nat}
    (h0 : 0 ∈ xs) (h72 : 72 ∉ xs) :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_anchor_ctx,
      (q9R4SelectionValuation xs).satisfies c := by
  intro c hc
  change c ∈ [[.pos 0], [.neg 72]] at hc
  rcases List.mem_cons.mp hc with hc | hc
  · subst c
    apply satisfies_of_true_literal
    simp [q9R4SelectionValuation, Sat.Valuation.neg]
    exact (selectionBool_true_iff xs 0).2 h0
  · have heq : c = [.neg 72] := List.mem_singleton.mp hc
    subst c
    apply satisfies_of_true_literal
    simp [q9R4SelectionValuation, Sat.Valuation.neg]
    simpa [selectionBool] using h72

lemma q9_r4_constructive_blocks_satisfied
    {xs : List Nat} (hdist : q9EdgeDistinct xs)
    (hbaseCount : prefixCount (fun i => !(selectionBool xs i)) 73 ≤ 64)
    (hatleastCount : prefixCount (q9OddComplementBool xs) 36 ≤ 32)
    (hatmostCount : prefixCount (q9OddSelectionBool xs) 36 ≤ 4)
    (h0 : 0 ∈ xs) (h72 : 72 ∉ xs) :
    (∀ c ∈ collisionTreeFlatten
        Erdos811Q9NoInfR4CNF.q9_noinf_r4_collision_tree,
      (q9R4SelectionValuation xs).satisfies c) ∧
    (∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx,
      (q9R4SelectionValuation xs).satisfies c) ∧
    (∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_anchor_ctx,
      (q9R4SelectionValuation xs).satisfies c) ∧
    (∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_eq_atleast_ctx,
      (q9R4SelectionValuation xs).satisfies c) ∧
    (∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_eq_atmost_ctx,
      (q9R4SelectionValuation xs).satisfies c) := by
  have hblocks := q9_r4_constructive_counter_blocks
    (xs := xs) hbaseCount hatleastCount hatmostCount
  exact ⟨q9R4_collision_tree_satisfied_constructive hdist,
    hblocks.1, q9_r4_anchor_satisfied_constructive h0 h72,
    hblocks.2.1, hblocks.2.2⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma q9_r4_collision_prefix_satisfied_constructive
    {xs : List Nat} (hdist : q9EdgeDistinct xs) :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_collision_ctx,
      (q9R4SelectionValuation xs).satisfies c := by
  rw [← q9_r4_collision_tree_flatten]
  exact q9R4_collision_tree_satisfied_constructive hdist

/- If a separate finite audit supplies the five-way clause-membership
   partition, the block theorem above assembles it into full parsed-CNF
   satisfaction.  Keeping this implication independent avoids re-running the
   96k-clause membership computation during ordinary elaboration. -/
lemma q9_r4_cnf_satisfied_of_partition
    {xs : List Nat} (hdist : q9EdgeDistinct xs)
    (hbaseCount : prefixCount (fun i => !(selectionBool xs i)) 73 ≤ 64)
    (hatleastCount : prefixCount (q9OddComplementBool xs) 36 ≤ 32)
    (hatmostCount : prefixCount (q9OddSelectionBool xs) 36 ≤ 4)
    (h0 : 0 ∈ xs) (h72 : 72 ∉ xs)
    (hpartition : ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_ctx,
      c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_collision_ctx ∨
      c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx ∨
      c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_anchor_ctx ∨
      c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_eq_atleast_ctx ∨
      c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_eq_atmost_ctx) :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_ctx,
      (q9R4SelectionValuation xs).satisfies c := by
  rcases q9_r4_constructive_blocks_satisfied
      (xs := xs) hdist hbaseCount hatleastCount hatmostCount h0 h72 with
    ⟨hcollision, hbase, hanchor, hatleast, hatmost⟩
  intro c hc
  rcases hpartition c hc with hcollision' | hbase' | hanchor' | hatleast' | hatmost'
  · exact q9_r4_collision_prefix_satisfied_constructive hdist c hcollision'
  · exact hbase c hbase'
  · exact hanchor c hanchor'
  · exact hatleast c hatleast'
  · exact hatmost c hatmost'

lemma q9_r4_ctx_partition :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_ctx,
      c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_collision_ctx ∨
      c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx ∨
      c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_anchor_ctx ∨
      c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_eq_atleast_ctx ∨
      c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_eq_atmost_ctx := by
  intro c hc
  change c ∈ fmlaAppend
      (fmlaAppend
        (fmlaAppend
          (fmlaAppend
            Erdos811Q9NoInfR4CNF.q9_noinf_r4_collision_ctx
            Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx)
          Erdos811Q9NoInfR4CNF.q9_noinf_r4_anchor_ctx)
        Erdos811Q9NoInfR4CNF.q9_noinf_r4_eq_atleast_ctx)
      Erdos811Q9NoInfR4CNF.q9_noinf_r4_eq_atmost_ctx at hc
  rcases fmlaAppend_mem.mp hc with hleft | hatmost
  · rcases fmlaAppend_mem.mp hleft with hleft | hatleast
    · rcases fmlaAppend_mem.mp hleft with hleft | hanchor
      · rcases fmlaAppend_mem.mp hleft with hcollision | hbase
        · exact Or.inl hcollision
        · exact Or.inr (Or.inl hbase)
      · exact Or.inr (Or.inr (Or.inl hanchor))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hatleast)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hatmost)))

lemma q9_r4_cnf_satisfied_constructive
    {xs : List Nat} (hdist : q9EdgeDistinct xs)
    (hbaseCount : prefixCount (fun i => !(selectionBool xs i)) 73 ≤ 64)
    (hatleastCount : prefixCount (q9OddComplementBool xs) 36 ≤ 32)
    (hatmostCount : prefixCount (q9OddSelectionBool xs) 36 ≤ 4)
    (h0 : 0 ∈ xs) (h72 : 72 ∉ xs) :
    ∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_ctx,
      (q9R4SelectionValuation xs).satisfies c := by
  exact q9_r4_cnf_satisfied_of_partition
    hdist hbaseCount hatleastCount hatmostCount h0 h72 q9_r4_ctx_partition

lemma q9_r5_anchor_satisfied_constructive {xs : List Nat}
    (h0 : 0 ∈ xs) (h72 : 72 ∉ xs) :
    ∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_anchor_ctx,
      (q9R5SelectionValuation xs).satisfies c := by
  intro c hc
  change c ∈ [[.pos 0], [.neg 72]] at hc
  rcases List.mem_cons.mp hc with hc | hc
  · subst c
    apply satisfies_of_true_literal
    simp [q9R5SelectionValuation, Sat.Valuation.neg]
    exact (selectionBool_true_iff xs 0).2 h0
  · have heq : c = [.neg 72] := List.mem_singleton.mp hc
    subst c
    apply satisfies_of_true_literal
    simp [q9R5SelectionValuation, Sat.Valuation.neg]
    simpa [selectionBool] using h72

lemma q9_r5_constructive_blocks_satisfied
    {xs : List Nat} (hdist : q9EdgeDistinct xs)
    (hbaseCount : prefixCount (fun i => !(selectionBool xs i)) 73 ≤ 64)
    (hatleastCount : prefixCount (q9OddComplementBool xs) 36 ≤ 31)
    (hatmostCount : prefixCount (q9OddSelectionBool xs) 36 ≤ 5)
    (h0 : 0 ∈ xs) (h72 : 72 ∉ xs) :
    (∀ c ∈ collisionTreeFlatten
        Erdos811Q9NoInfR5CNF.q9_noinf_r5_collision_tree,
      (q9R5SelectionValuation xs).satisfies c) ∧
    (∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_base_ctx,
      (q9R5SelectionValuation xs).satisfies c) ∧
    (∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_anchor_ctx,
      (q9R5SelectionValuation xs).satisfies c) ∧
    (∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_eq_atleast_ctx,
      (q9R5SelectionValuation xs).satisfies c) ∧
    (∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_eq_atmost_ctx,
      (q9R5SelectionValuation xs).satisfies c) := by
  have hblocks := q9_r5_constructive_counter_blocks
    (xs := xs) hbaseCount hatleastCount hatmostCount
  exact ⟨q9R5_collision_tree_satisfied_constructive hdist,
    hblocks.1, q9_r5_anchor_satisfied_constructive h0 h72,
    hblocks.2.1, hblocks.2.2⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma q9_r5_collision_prefix_satisfied_constructive
    {xs : List Nat} (hdist : q9EdgeDistinct xs) :
    ∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_collision_ctx,
      (q9R5SelectionValuation xs).satisfies c := by
  rw [← q9_r5_collision_tree_flatten]
  exact q9R5_collision_tree_satisfied_constructive hdist

lemma q9_r5_cnf_satisfied_of_partition
    {xs : List Nat} (hdist : q9EdgeDistinct xs)
    (hbaseCount : prefixCount (fun i => !(selectionBool xs i)) 73 ≤ 64)
    (hatleastCount : prefixCount (q9OddComplementBool xs) 36 ≤ 31)
    (hatmostCount : prefixCount (q9OddSelectionBool xs) 36 ≤ 5)
    (h0 : 0 ∈ xs) (h72 : 72 ∉ xs)
    (hpartition : ∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_ctx,
      c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_collision_ctx ∨
      c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_base_ctx ∨
      c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_anchor_ctx ∨
      c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_eq_atleast_ctx ∨
      c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_eq_atmost_ctx) :
    ∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_ctx,
      (q9R5SelectionValuation xs).satisfies c := by
  rcases q9_r5_constructive_blocks_satisfied
      (xs := xs) hdist hbaseCount hatleastCount hatmostCount h0 h72 with
    ⟨hcollision, hbase, hanchor, hatleast, hatmost⟩
  intro c hc
  rcases hpartition c hc with hcollision' | hbase' | hanchor' | hatleast' | hatmost'
  · exact q9_r5_collision_prefix_satisfied_constructive hdist c hcollision'
  · exact hbase c hbase'
  · exact hanchor c hanchor'
  · exact hatleast c hatleast'
  · exact hatmost c hatmost'

lemma q9_r5_ctx_partition :
    ∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_ctx,
      c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_collision_ctx ∨
      c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_base_ctx ∨
      c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_anchor_ctx ∨
      c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_eq_atleast_ctx ∨
      c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_eq_atmost_ctx := by
  intro c hc
  change c ∈ fmlaAppend
      (fmlaAppend
        (fmlaAppend
          (fmlaAppend
            Erdos811Q9NoInfR5CNF.q9_noinf_r5_collision_ctx
            Erdos811Q9NoInfR5CNF.q9_noinf_r5_base_ctx)
          Erdos811Q9NoInfR5CNF.q9_noinf_r5_anchor_ctx)
        Erdos811Q9NoInfR5CNF.q9_noinf_r5_eq_atleast_ctx)
      Erdos811Q9NoInfR5CNF.q9_noinf_r5_eq_atmost_ctx at hc
  rcases fmlaAppend_mem.mp hc with hleft | hatmost
  · rcases fmlaAppend_mem.mp hleft with hleft | hatleast
    · rcases fmlaAppend_mem.mp hleft with hleft | hanchor
      · rcases fmlaAppend_mem.mp hleft with hcollision | hbase
        · exact Or.inl hcollision
        · exact Or.inr (Or.inl hbase)
      · exact Or.inr (Or.inr (Or.inl hanchor))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hatleast)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hatmost)))

lemma q9_r5_cnf_satisfied_constructive
    {xs : List Nat} (hdist : q9EdgeDistinct xs)
    (hbaseCount : prefixCount (fun i => !(selectionBool xs i)) 73 ≤ 64)
    (hatleastCount : prefixCount (q9OddComplementBool xs) 36 ≤ 31)
    (hatmostCount : prefixCount (q9OddSelectionBool xs) 36 ≤ 5)
    (h0 : 0 ∈ xs) (h72 : 72 ∉ xs) :
    ∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_ctx,
      (q9R5SelectionValuation xs).satisfies c := by
  exact q9_r5_cnf_satisfied_of_partition
    hdist hbaseCount hatleastCount hatmostCount h0 h72 q9_r5_ctx_partition

end Erdos811Q9ConstructiveCNFAssembly
