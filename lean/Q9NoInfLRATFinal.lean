import Q9Symmetry
import Q9NoInfR4LRATStagedProof
import Q9NoInfR5LRATStagedProof

/-!
  Final q=9 LRAT entry point.

  The default theorem imports this file. The staged replay modules must still
  be compiled one at a time before the final `Q9R4Stage197`/`Q9R5Stage127`
  imports become available to the main build.
-/

namespace Erdos811

theorem q9_no_rainbow_staged_lrat :
    ¬ HasRainbowCopy (SimpleGraph.completeGraph (Fin 9)) q9Coloring := by
  exact q9_no_rainbow_lrat
    Erdos811Q9NoInfR4CNF.q9_noinf_r4_unsat_partitioned_staged
    Erdos811Q9NoInfR5CNF.q9_noinf_r5_unsat_partitioned_staged

#print axioms q9_no_rainbow_staged_lrat

end Erdos811
