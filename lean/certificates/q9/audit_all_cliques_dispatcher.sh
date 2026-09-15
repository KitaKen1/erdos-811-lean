#!/bin/zsh
set -e

# Source-only coverage audit for the q>=4 dispatcher.  This does not build
# Lean; it catches an accidentally omitted finite branch or a regression from
# the staged q=9 endpoint to the native theorem.
script_dir=${0:A:h}
lean_dir=${script_dir:h:h}
cd "$lean_dir"

fc=Erdos811FC.lean
for q in 4 5 6 7 8 9 10 11; do
  rg -q "^theorem q${q}_arbitrarily_large" "$fc"
  rg -q "q${q}_arbitrarily_large" "$fc"
done
rg -q '^theorem all_cliques_of_base_family' "$fc"
rg -q '12 ≤ q' "$fc"
rg -q 'probabilistic_witness_to_arbitrarily_large' "$fc"
rg -q 'q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨' "$fc"
rg -q '^import Q9NoInfLRATFinal' "$fc"
rg -q 'q9_no_rainbow_staged_lrat' "$fc"
rg -q 'erdos_811.variants.axenovich_clemen_all_cliques' "$fc"

print 'q>=4 dispatcher coverage OK (q=4..11 + q>=12)'
