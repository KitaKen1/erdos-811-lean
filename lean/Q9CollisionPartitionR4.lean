import Q9NoInfR4CNF

/-!
Full collision-prefix inclusion certificate for the q=9, r=4 CNF.

The generated theorem is deliberately kept in an explicit target: it creates
1,479 auxiliary 64-clause certificates and combines them with a balanced
subsumption proof, avoiding the one-shot 94,608-clause normalization timeout.
-/

set_option maxHeartbeats 2000000

namespace Erdos811Q9NoInfR4CNF

fmla_tree_subsumes_partition_def q9_collision_partition
  q9_noinf_r4_collision_tree
  (include_str "certificates/q9/q9_noinf_r4.cnf")
  0 94608 64

#print axioms q9_collision_partition

end Erdos811Q9NoInfR4CNF
