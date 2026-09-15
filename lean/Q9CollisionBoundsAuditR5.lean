import Q9Agreement

/-! r = 5 branch of the q = 9 collision-range audit.

This module deliberately contains only the r = 5 finite checker.  Keeping the
94,608-leaf `decide` proof in its own module makes the generated proof object
independent from the analogous r = 4 branch.
-/

namespace Erdos811Q9CollisionBoundsAuditR5

open Mathlib.Tactic.Sat
open Erdos811
open Erdos811Q9CNFSemantics
open Erdos811Q9CNFBridge
open Erdos811Q9Agreement

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma q9_r5_collision_bounds_tree :
    ∀ c ∈ collisionTreeFlatten
        Erdos811Q9NoInfR5CNF.q9_noinf_r5_collision_tree,
      Q9CollisionClause c ∧ clauseIndicesBelow73 c := by
  apply collisionTreeBoundedAll_true
  decide

set_option maxRecDepth 1000000 in
lemma q9R5_collision_tree_satisfied_constructive
    {xs : List Nat} (hdist : q9EdgeDistinct xs) :
    ∀ c ∈ collisionTreeFlatten
        Erdos811Q9NoInfR5CNF.q9_noinf_r5_collision_tree,
      (q9R5SelectionValuation xs).satisfies c := by
  intro c hc
  obtain ⟨hshape, hbound⟩ := q9_r5_collision_bounds_tree c hc
  exact q9R5_collision_satisfied_constructive hdist hshape hbound

end Erdos811Q9CollisionBoundsAuditR5
