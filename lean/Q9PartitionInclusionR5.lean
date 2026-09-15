import Q9CollisionPartitionR5
import Q9SATtoGraph

/-! Compose the q=9, r=5 collision partition with its four tail blocks. -/

namespace Erdos811Q9NoInfR5CNF

open Mathlib.Tactic.Sat
open Erdos811Q9SATtoGraph

lemma ctx_subsumes_collision :
    q9_noinf_r5_ctx.subsumes q9_noinf_r5_collision_ctx := by
  change (fmlaAppend
      (fmlaAppend
        (fmlaAppend
          (fmlaAppend q9_noinf_r5_collision_ctx q9_noinf_r5_base_ctx)
          q9_noinf_r5_anchor_ctx)
        q9_noinf_r5_eq_atleast_ctx)
      q9_noinf_r5_eq_atmost_ctx).subsumes q9_noinf_r5_collision_ctx
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_left_component
  exact Sat.Fmla.subsumes_self _

lemma ctx_subsumes_base :
    q9_noinf_r5_ctx.subsumes q9_noinf_r5_base_ctx := by
  change (fmlaAppend
      (fmlaAppend
        (fmlaAppend
          (fmlaAppend q9_noinf_r5_collision_ctx q9_noinf_r5_base_ctx)
          q9_noinf_r5_anchor_ctx)
        q9_noinf_r5_eq_atleast_ctx)
      q9_noinf_r5_eq_atmost_ctx).subsumes q9_noinf_r5_base_ctx
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_right_component
  exact Sat.Fmla.subsumes_self _

lemma ctx_subsumes_anchor :
    q9_noinf_r5_ctx.subsumes q9_noinf_r5_anchor_ctx := by
  change (fmlaAppend
      (fmlaAppend
        (fmlaAppend
          (fmlaAppend q9_noinf_r5_collision_ctx q9_noinf_r5_base_ctx)
          q9_noinf_r5_anchor_ctx)
        q9_noinf_r5_eq_atleast_ctx)
      q9_noinf_r5_eq_atmost_ctx).subsumes q9_noinf_r5_anchor_ctx
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_right_component
  exact Sat.Fmla.subsumes_self _

lemma ctx_subsumes_atleast :
    q9_noinf_r5_ctx.subsumes q9_noinf_r5_eq_atleast_ctx := by
  change (fmlaAppend
      (fmlaAppend
        (fmlaAppend
          (fmlaAppend q9_noinf_r5_collision_ctx q9_noinf_r5_base_ctx)
          q9_noinf_r5_anchor_ctx)
        q9_noinf_r5_eq_atleast_ctx)
      q9_noinf_r5_eq_atmost_ctx).subsumes q9_noinf_r5_eq_atleast_ctx
  apply fmlaAppend_subsumes_left_component
  apply fmlaAppend_subsumes_right_component
  exact Sat.Fmla.subsumes_self _

lemma ctx_subsumes_atmost :
    q9_noinf_r5_ctx.subsumes q9_noinf_r5_eq_atmost_ctx := by
  change (fmlaAppend
      (fmlaAppend
        (fmlaAppend
          (fmlaAppend q9_noinf_r5_collision_ctx q9_noinf_r5_base_ctx)
          q9_noinf_r5_anchor_ctx)
        q9_noinf_r5_eq_atleast_ctx)
      q9_noinf_r5_eq_atmost_ctx).subsumes q9_noinf_r5_eq_atmost_ctx
  apply fmlaAppend_subsumes_right_component
  exact Sat.Fmla.subsumes_self _

def q9_r5_partition_ranges : List (Nat × Nat) :=
  let collisionCount := (94608 + 63) / 64
  let collision := (List.range collisionCount).map (fun i =>
    (i * 64, min 64 (94608 - i * 64)))
  collision ++
    [(94608, 1097), (95705, 2), (95707, 284), (95991, 336)]

fmla_append_partition_subsumes_def q9_full_partition
  q9_noinf_r5_ctx q9_noinf_r5_collision_ctx q9_collision_partition
  (include_str "certificates/q9/q9_noinf_r5.cnf")
  0 94608 64 1097 2 284 336
  collision_lift ctx_subsumes_collision
  base_lift ctx_subsumes_base
  anchor_lift ctx_subsumes_anchor
  atleast_lift ctx_subsumes_atleast
  atmost_lift ctx_subsumes_atmost

#print axioms q9_full_partition

end Erdos811Q9NoInfR5CNF
