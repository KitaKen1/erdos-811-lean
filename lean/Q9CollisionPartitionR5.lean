import Q9NoInfR5CNF

/-! Full collision-prefix inclusion certificate for the q=9, r=5 branch. -/

set_option maxHeartbeats 2000000

namespace Erdos811Q9NoInfR5CNF

fmla_tree_subsumes_partition_def q9_collision_partition
  q9_noinf_r5_collision_tree
  (include_str "certificates/q9/q9_noinf_r5.cnf")
  0 94608 64

#print axioms q9_collision_partition

end Erdos811Q9NoInfR5CNF
