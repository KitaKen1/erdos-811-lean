import Q9CNFBridge

/-! Constructive counter valuations for the finite q=9 sequential-counter
    blocks.  The vertex variables are the selected set; each auxiliary
    variable is decoded from the same finite prefix-count predicate that the
    DIMACS encoder uses.  Collision-clause agreement is intentionally kept as
    a separate next step because it only needs the vertex-variable projection.
-/

namespace Erdos811Q9ConstructiveValuation

open Mathlib.Tactic.Sat
open Erdos811
open Erdos811Q9SeqCounter
open Erdos811Q9CNFSemantics
open Erdos811Q9CNFBridge

set_option maxRecDepth 100000 in
lemma q9_r4_constructive_counter_blocks
    {xs : List Nat}
    (hbaseCount : prefixCount (fun i => !(selectionBool xs i)) 73 ≤ 64)
    (hatleastCount : prefixCount (q9OddComplementBool xs) 36 ≤ 32)
    (hatmostCount : prefixCount (q9OddSelectionBool xs) 36 ≤ 4) :
    (∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_base_ctx,
      (q9R4SelectionValuation xs).satisfies c) ∧
    (∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_eq_atleast_ctx,
      (q9R4SelectionValuation xs).satisfies c) ∧
    (∀ c ∈ Erdos811Q9NoInfR4CNF.q9_noinf_r4_eq_atmost_ctx,
      (q9R4SelectionValuation xs).satisfies c) := by
  refine ⟨?_, ?_, ?_⟩
  · apply q9_r4_base_satisfied
      (v := q9R4SelectionValuation xs)
      (x := fun i => !(selectionBool xs i))
    · intro i hi
      exact q9R4SelectionValuation_input xs i hi
    · intro k j hk hj
      exact q9R4SelectionValuation_base_aux xs k j hk hj
    · exact hbaseCount
  · apply q9_r4_eq_atleast_satisfied
      (v := q9R4SelectionValuation xs)
      (x := q9OddComplementBool xs)
    · intro j hj
      exact q9R4SelectionValuation_odd_neg_input xs j hj
    · intro k j hk hj
      exact q9R4SelectionValuation_atleast_aux xs k j hk hj
    · exact hatleastCount
  · apply q9_r4_eq_atmost_satisfied
      (v := q9R4SelectionValuation xs)
      (x := q9OddSelectionBool xs)
    · intro j hj
      exact q9R4SelectionValuation_odd_pos_input xs j hj
    · intro k j hk hj
      exact q9R4SelectionValuation_atmost_aux xs k j hk hj
    · exact hatmostCount

set_option maxRecDepth 100000 in
lemma q9_r5_constructive_counter_blocks
    {xs : List Nat}
    (hbaseCount : prefixCount (fun i => !(selectionBool xs i)) 73 ≤ 64)
    (hatleastCount : prefixCount (q9OddComplementBool xs) 36 ≤ 31)
    (hatmostCount : prefixCount (q9OddSelectionBool xs) 36 ≤ 5) :
    (∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_base_ctx,
      (q9R5SelectionValuation xs).satisfies c) ∧
    (∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_eq_atleast_ctx,
      (q9R5SelectionValuation xs).satisfies c) ∧
    (∀ c ∈ Erdos811Q9NoInfR5CNF.q9_noinf_r5_eq_atmost_ctx,
      (q9R5SelectionValuation xs).satisfies c) := by
  refine ⟨?_, ?_, ?_⟩
  · apply q9_r5_base_satisfied
      (v := q9R5SelectionValuation xs)
      (x := fun i => !(selectionBool xs i))
    · intro i hi
      exact q9R5SelectionValuation_input xs i hi
    · intro k j hk hj
      exact q9R5SelectionValuation_base_aux xs k j hk hj
    · exact hbaseCount
  · apply q9_r5_eq_atleast_satisfied
      (v := q9R5SelectionValuation xs)
      (x := q9OddComplementBool xs)
    · intro j hj
      exact q9R5SelectionValuation_odd_neg_input xs j hj
    · intro k j hk hj
      exact q9R5SelectionValuation_atleast_aux xs k j hk hj
    · exact hatleastCount
  · apply q9_r5_eq_atmost_satisfied
      (v := q9R5SelectionValuation xs)
      (x := q9OddSelectionBool xs)
    · intro j hj
      exact q9R5SelectionValuation_odd_pos_input xs j hj
    · intro k j hk hj
      exact q9R5SelectionValuation_atmost_aux xs k j hk hj
    · exact hatmostCount

end Erdos811Q9ConstructiveValuation
