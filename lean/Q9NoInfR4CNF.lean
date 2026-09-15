import Q9LRATChunked

/-! The parsed q=9, r=4 CNF, exposed without replaying its LRAT trace. -/

namespace Erdos811Q9NoInfR4CNF

/- The collision slice is exposed through the balanced tree generated from the
   same DIMACS interval.  This makes its identity with the tree flattening
   definitional, while the remaining four slices stay ordinary parsed lists. -/
sat_cnf_tree_def q9_noinf_r4_collision_tree
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  0 94608

noncomputable def q9_noinf_r4_collision_ctx : Sat.Fmla :=
  Mathlib.Tactic.Sat.fmlaTreeFlattenOpaque q9_noinf_r4_collision_tree

sat_cnf_slice_def q9_noinf_r4_base_ctx
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  94608 1097

sat_cnf_slice_def q9_noinf_r4_eq_ctx
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  95707 512

sat_cnf_slice_def q9_noinf_r4_eq_atleast_ctx
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  95707 228

sat_cnf_slice_def q9_noinf_r4_eq_atmost_ctx
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  95935 284

sat_cnf_slice_def q9_noinf_r4_anchor_ctx
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  95705 2

sat_cnf_slice_def q9_noinf_r4_base_chunk0
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  94608 64

sat_cnf_slice_def q9_noinf_r4_base_chunk1
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  94672 64

sat_cnf_slice_def q9_noinf_r4_base_chunk2
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  94736 64

sat_cnf_slice_def q9_noinf_r4_base_chunk3
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  94800 64

sat_cnf_slice_def q9_noinf_r4_base_chunk4
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  94864 64

sat_cnf_slice_def q9_noinf_r4_base_chunk5
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  94928 64

sat_cnf_slice_def q9_noinf_r4_base_chunk6
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  94992 64

sat_cnf_slice_def q9_noinf_r4_base_chunk7
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  95056 64

sat_cnf_slice_def q9_noinf_r4_base_chunk8
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  95120 64

sat_cnf_slice_def q9_noinf_r4_base_chunk9
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  95184 64

sat_cnf_slice_def q9_noinf_r4_base_chunk10
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  95248 64

sat_cnf_slice_def q9_noinf_r4_base_chunk11
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  95312 64

sat_cnf_slice_def q9_noinf_r4_base_chunk12
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  95376 64

sat_cnf_slice_def q9_noinf_r4_base_chunk13
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  95440 64

sat_cnf_slice_def q9_noinf_r4_base_chunk14
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  95504 64

sat_cnf_slice_def q9_noinf_r4_base_chunk15
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  95568 64

sat_cnf_slice_def q9_noinf_r4_base_chunk16
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  95632 64

sat_cnf_slice_def q9_noinf_r4_base_chunk17
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  95696 9

noncomputable def q9_noinf_r4_ctx : Sat.Fmla :=
  Mathlib.Tactic.Sat.fmlaAppend
    (Mathlib.Tactic.Sat.fmlaAppend
      (Mathlib.Tactic.Sat.fmlaAppend
        (Mathlib.Tactic.Sat.fmlaAppend
          q9_noinf_r4_collision_ctx q9_noinf_r4_base_ctx)
        q9_noinf_r4_anchor_ctx)
      q9_noinf_r4_eq_atleast_ctx)
    q9_noinf_r4_eq_atmost_ctx

end Erdos811Q9NoInfR4CNF
