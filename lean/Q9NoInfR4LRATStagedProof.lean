import Q9R4Stage197

/-!
  Final wrapper for the staged q=9, r=4 LRAT replay.

  `Q9R4Stage197` is intentionally compiled separately by
  `certificates/q9/compile_lrat_stages.sh`; importing this file before that
  job finishes is expected to fail with a missing module. -/

namespace Erdos811Q9NoInfR4CNF

theorem q9_noinf_r4_unsat_partitioned_staged :
    q9_noinf_r4_ctx.proof ([]) :=
  q9_r4_stage197

#print axioms q9_noinf_r4_unsat_partitioned_staged

end Erdos811Q9NoInfR4CNF
