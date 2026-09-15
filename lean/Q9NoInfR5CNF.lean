import Q9LRATChunked

/-! Parsed q=9, r=5 finite-branch CNF, exposed as a Lean formula.

This target deliberately stops before LRAT replay: it gives the semantic
bridge a small, reproducible formula constant while the much larger replay
can be benchmarked independently.
-/

namespace Erdos811Q9NoInfR5CNF

/- The collision slice is exposed by flattening the balanced tree generated
   from the same DIMACS interval; this keeps the tree/slice identity direct. -/
sat_cnf_tree_def q9_noinf_r5_collision_tree
  (include_str "certificates/q9/q9_noinf_r5.cnf")
  0 94608

noncomputable def q9_noinf_r5_collision_ctx : Sat.Fmla :=
  Mathlib.Tactic.Sat.fmlaTreeFlattenOpaque q9_noinf_r5_collision_tree

sat_cnf_slice_def q9_noinf_r5_base_ctx
  (include_str "certificates/q9/q9_noinf_r5.cnf")
  94608 1097

sat_cnf_slice_def q9_noinf_r5_eq_ctx
  (include_str "certificates/q9/q9_noinf_r5.cnf")
  95707 620

sat_cnf_slice_def q9_noinf_r5_eq_atleast_ctx
  (include_str "certificates/q9/q9_noinf_r5.cnf")
  95707 284

sat_cnf_slice_def q9_noinf_r5_eq_atmost_ctx
  (include_str "certificates/q9/q9_noinf_r5.cnf")
  95991 336

sat_cnf_slice_def q9_noinf_r5_anchor_ctx
  (include_str "certificates/q9/q9_noinf_r5.cnf")
  95705 2

noncomputable def q9_noinf_r5_ctx : Sat.Fmla :=
  Mathlib.Tactic.Sat.fmlaAppend
    (Mathlib.Tactic.Sat.fmlaAppend
      (Mathlib.Tactic.Sat.fmlaAppend
        (Mathlib.Tactic.Sat.fmlaAppend
          q9_noinf_r5_collision_ctx q9_noinf_r5_base_ctx)
        q9_noinf_r5_anchor_ctx)
      q9_noinf_r5_eq_atleast_ctx)
    q9_noinf_r5_eq_atmost_ctx

end Erdos811Q9NoInfR5CNF
