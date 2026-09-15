import Q9CollisionPartitionR4
import Q9SATtoGraph

/-!
Compose the full q=9, r=4 parsed-CNF context inclusion.

The collision prefix is supplied by `q9_collision_partition`; the four tail
blocks are lifted through the nested `fmlaAppend` context and then combined by
the partition-aware meta command.  This target is explicit because generating
the 1,483-range proof creates a sizeable (but replayable) environment.
-/

namespace Erdos811Q9NoInfR4CNF

open Mathlib.Tactic.Sat
open Erdos811Q9SATtoGraph

lemma ctx_subsumes_collision :
    q9_noinf_r4_ctx.subsumes q9_noinf_r4_collision_ctx := by
  change (fmlaAppend
      (fmlaAppend
        (fmlaAppend
          (fmlaAppend q9_noinf_r4_collision_ctx q9_noinf_r4_base_ctx)
          q9_noinf_r4_anchor_ctx)
        q9_noinf_r4_eq_atleast_ctx)
      q9_noinf_r4_eq_atmost_ctx).subsumes q9_noinf_r4_collision_ctx
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_left_component
  exact Sat.Fmla.subsumes_self _

lemma ctx_subsumes_base :
    q9_noinf_r4_ctx.subsumes q9_noinf_r4_base_ctx := by
  change (fmlaAppend
      (fmlaAppend
        (fmlaAppend
          (fmlaAppend q9_noinf_r4_collision_ctx q9_noinf_r4_base_ctx)
          q9_noinf_r4_anchor_ctx)
        q9_noinf_r4_eq_atleast_ctx)
      q9_noinf_r4_eq_atmost_ctx).subsumes q9_noinf_r4_base_ctx
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_right_component
  exact Sat.Fmla.subsumes_self _

lemma ctx_subsumes_anchor :
    q9_noinf_r4_ctx.subsumes q9_noinf_r4_anchor_ctx := by
  change (fmlaAppend
      (fmlaAppend
        (fmlaAppend
          (fmlaAppend q9_noinf_r4_collision_ctx q9_noinf_r4_base_ctx)
          q9_noinf_r4_anchor_ctx)
        q9_noinf_r4_eq_atleast_ctx)
      q9_noinf_r4_eq_atmost_ctx).subsumes q9_noinf_r4_anchor_ctx
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_right_component
  exact Sat.Fmla.subsumes_self _

lemma ctx_subsumes_atleast :
    q9_noinf_r4_ctx.subsumes q9_noinf_r4_eq_atleast_ctx := by
  change (fmlaAppend
      (fmlaAppend
        (fmlaAppend
          (fmlaAppend q9_noinf_r4_collision_ctx q9_noinf_r4_base_ctx)
          q9_noinf_r4_anchor_ctx)
        q9_noinf_r4_eq_atleast_ctx)
      q9_noinf_r4_eq_atmost_ctx).subsumes q9_noinf_r4_eq_atleast_ctx
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_right_component
  exact Sat.Fmla.subsumes_self _

lemma ctx_subsumes_atmost :
    q9_noinf_r4_ctx.subsumes q9_noinf_r4_eq_atmost_ctx := by
  change (fmlaAppend
      (fmlaAppend
        (fmlaAppend
          (fmlaAppend q9_noinf_r4_collision_ctx q9_noinf_r4_base_ctx)
          q9_noinf_r4_anchor_ctx)
        q9_noinf_r4_eq_atleast_ctx)
      q9_noinf_r4_eq_atmost_ctx).subsumes q9_noinf_r4_eq_atmost_ctx
  apply fmlaAppend_subsumes_right_component
  exact Sat.Fmla.subsumes_self _

/- The exact contiguous range list consumed by the partition-aware LRAT
   command.  Keeping it as a computable term avoids embedding 1,483 pairs in
   the source while still letting the elaborator evaluate and validate every
   boundary. -/
def q9_r4_partition_ranges : List (Nat × Nat) :=
  let collisionCount := (94608 + 63) / 64
  let collision := (List.range collisionCount).map (fun i =>
    (i * 64, min 64 (94608 - i * 64)))
  collision ++
    [(94608, 1097), (95705, 2), (95707, 228), (95935, 284)]

fmla_append_partition_subsumes_def q9_full_partition
  q9_noinf_r4_ctx q9_noinf_r4_collision_ctx q9_collision_partition
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  0 94608 64 1097 2 228 284
  collision_lift ctx_subsumes_collision
  base_lift ctx_subsumes_base
  anchor_lift ctx_subsumes_anchor
  atleast_lift ctx_subsumes_atleast
  atmost_lift ctx_subsumes_atmost

#print axioms q9_full_partition

end Erdos811Q9NoInfR4CNF
